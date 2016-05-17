# doublerebel/publictransport

Golang http.Server and http.Transport with many more public methods and fields.

For when you really have to get to work and Golang stdlib is blocking your usual route.

## Introduction

Golang creates a lot of nice structures to manage persistent connections, and keeps them all under the hood.  Here we copy+paste enough of net/http to run a custom http.Server or http.Transport with the connection information exposed on Requests/Responses.  Based mostly off of master, but without contexts because they're kind of a hassle.

This way we can get notifications on connection close and manage connection-related information, as well as associating data with the appropriate requests.

I'm sure more could be exposed depending on what part of Server or Transport to customize.  However, we defer to as much of the stdlib net/http as possible.

## Warning

Associating connections with Requests/Responses is standard in many languages, but Golang is rather opinionated about public/private APIs, so use at your own risk.

## Example

[**doublerebel/fabio#feature/CopyHeaders**](https://github.com/doublerebel/fabio/commit/f52162615bce5a5ffc4db6243c27612537217ffe)

## Installation
```sh
go get doublerebel/publictransport
```

## License

MIT