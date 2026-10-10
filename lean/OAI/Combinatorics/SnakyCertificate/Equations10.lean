import OAI.Combinatorics.SnakyCertificate.Cache
import OAI.Combinatorics.SnakyCertificate.TableList

namespace OAI

namespace SnakyCertificate.Check

theorem verified_row_400 : fork [place ⟨283, 4, 2, 4⟩ cache_283, place ⟨252, 4, 2, 4⟩ cache_252, place ⟨176, 4, 2, 4⟩ cache_176, place ⟨197, 0, 6, 4⟩ cache_197, place ⟨283, 0, 6, 4⟩ cache_283, place ⟨245, 4, 2, 4⟩ cache_245] = cache_400 := by
  decide +kernel

theorem load_entry_400 : entryAt 400 = entry_400 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_400 : CacheEquation 400 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(400 < 6)), load_entry_400]
  change forkRow [placeRow ⟨283, 4, 2, 4⟩ (denote cache_283), placeRow ⟨252, 4, 2, 4⟩ (denote cache_252), placeRow ⟨176, 4, 2, 4⟩ (denote cache_176), placeRow ⟨197, 0, 6, 4⟩ (denote cache_197), placeRow ⟨283, 0, 6, 4⟩ (denote cache_283), placeRow ⟨245, 4, 2, 4⟩ (denote cache_245)] = denote cache_400
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_400

theorem verified_row_401 : fork [place ⟨24, 7, 3, 2⟩ cache_24, place ⟨286, 0, 4, 6⟩ cache_286, place ⟨364, 2, 4, 2⟩ cache_364, place ⟨319, 1, 3, 6⟩ cache_319] = cache_401 := by
  decide +kernel

theorem load_entry_401 : entryAt 401 = entry_401 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_401 : CacheEquation 401 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(401 < 6)), load_entry_401]
  change forkRow [placeRow ⟨24, 7, 3, 2⟩ (denote cache_24), placeRow ⟨286, 0, 4, 6⟩ (denote cache_286), placeRow ⟨364, 2, 4, 2⟩ (denote cache_364), placeRow ⟨319, 1, 3, 6⟩ (denote cache_319)] = denote cache_401
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_401

theorem verified_row_402 : fork [place ⟨29, 3, 3, 0⟩ cache_29, place ⟨384, 0, 5, 4⟩ cache_384] = cache_402 := by
  decide +kernel

theorem load_entry_402 : entryAt 402 = entry_402 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_402 : CacheEquation 402 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(402 < 6)), load_entry_402]
  change forkRow [placeRow ⟨29, 3, 3, 0⟩ (denote cache_29), placeRow ⟨384, 0, 5, 4⟩ (denote cache_384)] = denote cache_402
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_402

theorem verified_row_403 : fork [place ⟨202, 1, 4, 5⟩ cache_202, place ⟨180, 0, 4, 5⟩ cache_180, place ⟨314, 4, 5, 4⟩ cache_314, place ⟨63, 0, 3, 5⟩ cache_63, place ⟨388, 0, 3, 4⟩ cache_388] = cache_403 := by
  decide +kernel

theorem load_entry_403 : entryAt 403 = entry_403 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_403 : CacheEquation 403 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(403 < 6)), load_entry_403]
  change forkRow [placeRow ⟨202, 1, 4, 5⟩ (denote cache_202), placeRow ⟨180, 0, 4, 5⟩ (denote cache_180), placeRow ⟨314, 4, 5, 4⟩ (denote cache_314), placeRow ⟨63, 0, 3, 5⟩ (denote cache_63), placeRow ⟨388, 0, 3, 4⟩ (denote cache_388)] = denote cache_403
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_403

theorem verified_row_404 : fork [place ⟨82, 6, 2, 3⟩ cache_82, place ⟨388, 4, 4, 6⟩ cache_388] = cache_404 := by
  decide +kernel

theorem load_entry_404 : entryAt 404 = entry_404 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_404 : CacheEquation 404 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(404 < 6)), load_entry_404]
  change forkRow [placeRow ⟨82, 6, 2, 3⟩ (denote cache_82), placeRow ⟨388, 4, 4, 6⟩ (denote cache_388)] = denote cache_404
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_404

theorem verified_row_405 : fork [place ⟨391, 0, 4, 3⟩ cache_391, place ⟨301, 0, 5, 2⟩ cache_301, place ⟨42, 1, 4, 3⟩ cache_42] = cache_405 := by
  decide +kernel

theorem load_entry_405 : entryAt 405 = entry_405 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_405 : CacheEquation 405 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(405 < 6)), load_entry_405]
  change forkRow [placeRow ⟨391, 0, 4, 3⟩ (denote cache_391), placeRow ⟨301, 0, 5, 2⟩ (denote cache_301), placeRow ⟨42, 1, 4, 3⟩ (denote cache_42)] = denote cache_405
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_405

theorem verified_row_406 : fork [place ⟨295, 1, 4, 5⟩ cache_295, place ⟨172, 7, 4, 1⟩ cache_172, place ⟨245, 3, 4, 5⟩ cache_245, place ⟨197, 5, 4, 1⟩ cache_197, place ⟨236, 0, 5, 5⟩ cache_236, place ⟨176, 3, 4, 5⟩ cache_176, place ⟨364, 2, 4, 1⟩ cache_364] = cache_406 := by
  decide +kernel

theorem load_entry_406 : entryAt 406 = entry_406 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_406 : CacheEquation 406 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(406 < 6)), load_entry_406]
  change forkRow [placeRow ⟨295, 1, 4, 5⟩ (denote cache_295), placeRow ⟨172, 7, 4, 1⟩ (denote cache_172), placeRow ⟨245, 3, 4, 5⟩ (denote cache_245), placeRow ⟨197, 5, 4, 1⟩ (denote cache_197), placeRow ⟨236, 0, 5, 5⟩ (denote cache_236), placeRow ⟨176, 3, 4, 5⟩ (denote cache_176), placeRow ⟨364, 2, 4, 1⟩ (denote cache_364)] = denote cache_406
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_406

theorem verified_row_407 : fork [place ⟨285, 0, 3, 7⟩ cache_285, place ⟨314, 6, 5, 4⟩ cache_314] = cache_407 := by
  decide +kernel

theorem load_entry_407 : entryAt 407 = entry_407 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_407 : CacheEquation 407 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(407 < 6)), load_entry_407]
  change forkRow [placeRow ⟨285, 0, 3, 7⟩ (denote cache_285), placeRow ⟨314, 6, 5, 4⟩ (denote cache_314)] = denote cache_407
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_407

theorem verified_row_408 : fork [place ⟨357, 0, 5, 2⟩ cache_357, place ⟨229, 7, 2, 4⟩ cache_229, place ⟨223, 4, 2, 4⟩ cache_223, place ⟨223, 0, 6, 4⟩ cache_223] = cache_408 := by
  decide +kernel

theorem load_entry_408 : entryAt 408 = entry_408 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_408 : CacheEquation 408 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(408 < 6)), load_entry_408]
  change forkRow [placeRow ⟨357, 0, 5, 2⟩ (denote cache_357), placeRow ⟨229, 7, 2, 4⟩ (denote cache_229), placeRow ⟨223, 4, 2, 4⟩ (denote cache_223), placeRow ⟨223, 0, 6, 4⟩ (denote cache_223)] = denote cache_408
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_408

theorem verified_row_409 : fork [place ⟨136, 6, 4, 3⟩ cache_136, place ⟨384, 0, 5, 4⟩ cache_384, place ⟨133, 4, 4, 3⟩ cache_133, place ⟨110, 3, 4, 3⟩ cache_110] = cache_409 := by
  decide +kernel

theorem load_entry_409 : entryAt 409 = entry_409 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_409 : CacheEquation 409 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(409 < 6)), load_entry_409]
  change forkRow [placeRow ⟨136, 6, 4, 3⟩ (denote cache_136), placeRow ⟨384, 0, 5, 4⟩ (denote cache_384), placeRow ⟨133, 4, 4, 3⟩ (denote cache_133), placeRow ⟨110, 3, 4, 3⟩ (denote cache_110)] = denote cache_409
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_409

theorem verified_row_410 : fork [place ⟨0, 4, 5, 4⟩ cache_0, place ⟨405, 0, 3, 7⟩ cache_405] = cache_410 := by
  decide +kernel

theorem load_entry_410 : entryAt 410 = entry_410 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_410 : CacheEquation 410 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(410 < 6)), load_entry_410]
  change forkRow [placeRow ⟨0, 4, 5, 4⟩ (denote cache_0), placeRow ⟨405, 0, 3, 7⟩ (denote cache_405)] = denote cache_410
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_410

theorem verified_row_411 : fork [place ⟨252, 0, 7, 4⟩ cache_252, place ⟨263, 0, 7, 4⟩ cache_263, place ⟨300, 3, 3, 4⟩ cache_300, place ⟨379, 1, 7, 4⟩ cache_379, place ⟨173, 0, 7, 4⟩ cache_173, place ⟨246, 0, 7, 4⟩ cache_246] = cache_411 := by
  decide +kernel

theorem load_entry_411 : entryAt 411 = entry_411 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_411 : CacheEquation 411 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(411 < 6)), load_entry_411]
  change forkRow [placeRow ⟨252, 0, 7, 4⟩ (denote cache_252), placeRow ⟨263, 0, 7, 4⟩ (denote cache_263), placeRow ⟨300, 3, 3, 4⟩ (denote cache_300), placeRow ⟨379, 1, 7, 4⟩ (denote cache_379), placeRow ⟨173, 0, 7, 4⟩ (denote cache_173), placeRow ⟨246, 0, 7, 4⟩ (denote cache_246)] = denote cache_411
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_411

theorem verified_row_412 : fork [place ⟨0, 0, 0, 3⟩ cache_0, place ⟨403, 4, 3, 6⟩ cache_403] = cache_412 := by
  decide +kernel

theorem load_entry_412 : entryAt 412 = entry_412 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_412 : CacheEquation 412 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(412 < 6)), load_entry_412]
  change forkRow [placeRow ⟨0, 0, 0, 3⟩ (denote cache_0), placeRow ⟨403, 4, 3, 6⟩ (denote cache_403)] = denote cache_412
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_412

theorem verified_row_413 : fork [place ⟨3, 7, 4, 3⟩ cache_3, place ⟨403, 0, 4, 7⟩ cache_403] = cache_413 := by
  decide +kernel

theorem load_entry_413 : entryAt 413 = entry_413 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_413 : CacheEquation 413 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(413 < 6)), load_entry_413]
  change forkRow [placeRow ⟨3, 7, 4, 3⟩ (denote cache_3), placeRow ⟨403, 0, 4, 7⟩ (denote cache_403)] = denote cache_413
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_413

theorem verified_row_414 : fork [place ⟨374, 0, 2, 5⟩ cache_374, place ⟨199, 2, 4, 2⟩ cache_199, place ⟨185, 2, 4, 2⟩ cache_185] = cache_414 := by
  decide +kernel

theorem load_entry_414 : entryAt 414 = entry_414 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_414 : CacheEquation 414 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(414 < 6)), load_entry_414]
  change forkRow [placeRow ⟨374, 0, 2, 5⟩ (denote cache_374), placeRow ⟨199, 2, 4, 2⟩ (denote cache_199), placeRow ⟨185, 2, 4, 2⟩ (denote cache_185)] = denote cache_414
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_414

theorem verified_row_415 : fork [place ⟨177, 1, 4, 2⟩ cache_177, place ⟨164, 1, 4, 2⟩ cache_164, place ⟨205, 1, 5, 2⟩ cache_205, place ⟨384, 0, 3, 4⟩ cache_384, place ⟨371, 0, 5, 4⟩ cache_371] = cache_415 := by
  decide +kernel

theorem load_entry_415 : entryAt 415 = entry_415 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_415 : CacheEquation 415 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(415 < 6)), load_entry_415]
  change forkRow [placeRow ⟨177, 1, 4, 2⟩ (denote cache_177), placeRow ⟨164, 1, 4, 2⟩ (denote cache_164), placeRow ⟨205, 1, 5, 2⟩ (denote cache_205), placeRow ⟨384, 0, 3, 4⟩ (denote cache_384), placeRow ⟨371, 0, 5, 4⟩ (denote cache_371)] = denote cache_415
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_415

theorem verified_row_416 : fork [place ⟨176, 2, 5, 4⟩ cache_176, place ⟨385, 4, 1, 4⟩ cache_385, place ⟨197, 4, 1, 4⟩ cache_197, place ⟨295, 0, 5, 4⟩ cache_295, place ⟨245, 2, 5, 4⟩ cache_245, place ⟨220, 2, 5, 4⟩ cache_220] = cache_416 := by
  decide +kernel

theorem load_entry_416 : entryAt 416 = entry_416 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_416 : CacheEquation 416 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(416 < 6)), load_entry_416]
  change forkRow [placeRow ⟨176, 2, 5, 4⟩ (denote cache_176), placeRow ⟨385, 4, 1, 4⟩ (denote cache_385), placeRow ⟨197, 4, 1, 4⟩ (denote cache_197), placeRow ⟨295, 0, 5, 4⟩ (denote cache_295), placeRow ⟨245, 2, 5, 4⟩ (denote cache_245), placeRow ⟨220, 2, 5, 4⟩ (denote cache_220)] = denote cache_416
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_416

theorem verified_row_417 : fork [place ⟨409, 0, 2, 4⟩ cache_409, place ⟨11, 1, 4, 2⟩ cache_11, place ⟨270, 4, 4, 2⟩ cache_270] = cache_417 := by
  decide +kernel

theorem load_entry_417 : entryAt 417 = entry_417 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_417 : CacheEquation 417 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(417 < 6)), load_entry_417]
  change forkRow [placeRow ⟨409, 0, 2, 4⟩ (denote cache_409), placeRow ⟨11, 1, 4, 2⟩ (denote cache_11), placeRow ⟨270, 4, 4, 2⟩ (denote cache_270)] = denote cache_417
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_417

theorem verified_row_418 : fork [place ⟨68, 4, 1, 3⟩ cache_68, place ⟨62, 6, 1, 3⟩ cache_62, place ⟨147, 6, 1, 3⟩ cache_147, place ⟨413, 0, 4, 2⟩ cache_413] = cache_418 := by
  decide +kernel

theorem load_entry_418 : entryAt 418 = entry_418 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_418 : CacheEquation 418 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(418 < 6)), load_entry_418]
  change forkRow [placeRow ⟨68, 4, 1, 3⟩ (denote cache_68), placeRow ⟨62, 6, 1, 3⟩ (denote cache_62), placeRow ⟨147, 6, 1, 3⟩ (denote cache_147), placeRow ⟨413, 0, 4, 2⟩ (denote cache_413)] = denote cache_418
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_418

theorem verified_row_419 : fork [place ⟨243, 0, 4, 2⟩ cache_243, place ⟨164, 1, 4, 2⟩ cache_164, place ⟨402, 0, 2, 4⟩ cache_402, place ⟨253, 0, 2, 4⟩ cache_253, place ⟨377, 0, 2, 4⟩ cache_377] = cache_419 := by
  decide +kernel

theorem load_entry_419 : entryAt 419 = entry_419 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_419 : CacheEquation 419 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(419 < 6)), load_entry_419]
  change forkRow [placeRow ⟨243, 0, 4, 2⟩ (denote cache_243), placeRow ⟨164, 1, 4, 2⟩ (denote cache_164), placeRow ⟨402, 0, 2, 4⟩ (denote cache_402), placeRow ⟨253, 0, 2, 4⟩ (denote cache_253), placeRow ⟨377, 0, 2, 4⟩ (denote cache_377)] = denote cache_419
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_419

theorem verified_row_420 : fork [place ⟨29, 3, 3, 0⟩ cache_29, place ⟨415, 0, 6, 4⟩ cache_415] = cache_420 := by
  decide +kernel

theorem load_entry_420 : entryAt 420 = entry_420 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_420 : CacheEquation 420 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(420 < 6)), load_entry_420]
  change forkRow [placeRow ⟨29, 3, 3, 0⟩ (denote cache_29), placeRow ⟨415, 0, 6, 4⟩ (denote cache_415)] = denote cache_420
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_420

theorem verified_row_421 : fork [place ⟨24, 6, 2, 3⟩ cache_24, place ⟨397, 1, 5, 3⟩ cache_397, place ⟨25, 6, 2, 3⟩ cache_25, place ⟨241, 4, 2, 4⟩ cache_241] = cache_421 := by
  decide +kernel

theorem load_entry_421 : entryAt 421 = entry_421 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_421 : CacheEquation 421 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(421 < 6)), load_entry_421]
  change forkRow [placeRow ⟨24, 6, 2, 3⟩ (denote cache_24), placeRow ⟨397, 1, 5, 3⟩ (denote cache_397), placeRow ⟨25, 6, 2, 3⟩ (denote cache_25), placeRow ⟨241, 4, 2, 4⟩ (denote cache_241)] = denote cache_421
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_421

theorem verified_row_422 : fork [place ⟨45, 1, 3, 7⟩ cache_45, place ⟨106, 6, 2, 3⟩ cache_106, place ⟨419, 1, 6, 6⟩ cache_419] = cache_422 := by
  decide +kernel

theorem load_entry_422 : entryAt 422 = entry_422 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_422 : CacheEquation 422 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(422 < 6)), load_entry_422]
  change forkRow [placeRow ⟨45, 1, 3, 7⟩ (denote cache_45), placeRow ⟨106, 6, 2, 3⟩ (denote cache_106), placeRow ⟨419, 1, 6, 6⟩ (denote cache_419)] = denote cache_422
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_422

theorem verified_row_423 : fork [place ⟨378, 4, 2, 4⟩ cache_378, place ⟨386, 0, 5, 4⟩ cache_386, place ⟨226, 3, 3, 5⟩ cache_226, place ⟨386, 4, 2, 4⟩ cache_386, place ⟨378, 0, 5, 4⟩ cache_378] = cache_423 := by
  decide +kernel

theorem load_entry_423 : entryAt 423 = entry_423 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_423 : CacheEquation 423 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(423 < 6)), load_entry_423]
  change forkRow [placeRow ⟨378, 4, 2, 4⟩ (denote cache_378), placeRow ⟨386, 0, 5, 4⟩ (denote cache_386), placeRow ⟨226, 3, 3, 5⟩ (denote cache_226), placeRow ⟨386, 4, 2, 4⟩ (denote cache_386), placeRow ⟨378, 0, 5, 4⟩ (denote cache_378)] = denote cache_423
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_423

theorem verified_row_424 : fork [place ⟨55, 1, 4, 5⟩ cache_55, place ⟨394, 0, 6, 4⟩ cache_394, place ⟨216, 3, 4, 5⟩ cache_216] = cache_424 := by
  decide +kernel

theorem load_entry_424 : entryAt 424 = entry_424 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_424 : CacheEquation 424 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(424 < 6)), load_entry_424]
  change forkRow [placeRow ⟨55, 1, 4, 5⟩ (denote cache_55), placeRow ⟨394, 0, 6, 4⟩ (denote cache_394), placeRow ⟨216, 3, 4, 5⟩ (denote cache_216)] = denote cache_424
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_424

theorem verified_row_425 : fork [place ⟨386, 0, 5, 4⟩ cache_386, place ⟨226, 1, 4, 5⟩ cache_226, place ⟨378, 4, 2, 4⟩ cache_378, place ⟨378, 0, 5, 4⟩ cache_378, place ⟨386, 4, 2, 4⟩ cache_386] = cache_425 := by
  decide +kernel

theorem load_entry_425 : entryAt 425 = entry_425 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_425 : CacheEquation 425 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(425 < 6)), load_entry_425]
  change forkRow [placeRow ⟨386, 0, 5, 4⟩ (denote cache_386), placeRow ⟨226, 1, 4, 5⟩ (denote cache_226), placeRow ⟨378, 4, 2, 4⟩ (denote cache_378), placeRow ⟨378, 0, 5, 4⟩ (denote cache_378), placeRow ⟨386, 4, 2, 4⟩ (denote cache_386)] = denote cache_425
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_425

theorem verified_row_426 : fork [place ⟨300, 6, 4, 1⟩ cache_300, place ⟨252, 1, 4, 5⟩ cache_252, place ⟨397, 0, 3, 4⟩ cache_397, place ⟨291, 1, 4, 1⟩ cache_291, place ⟨328, 0, 4, 5⟩ cache_328, place ⟨319, 1, 3, 5⟩ cache_319] = cache_426 := by
  decide +kernel

theorem load_entry_426 : entryAt 426 = entry_426 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_426 : CacheEquation 426 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(426 < 6)), load_entry_426]
  change forkRow [placeRow ⟨300, 6, 4, 1⟩ (denote cache_300), placeRow ⟨252, 1, 4, 5⟩ (denote cache_252), placeRow ⟨397, 0, 3, 4⟩ (denote cache_397), placeRow ⟨291, 1, 4, 1⟩ (denote cache_291), placeRow ⟨328, 0, 4, 5⟩ (denote cache_328), placeRow ⟨319, 1, 3, 5⟩ (denote cache_319)] = denote cache_426
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_426

theorem verified_row_427 : fork [place ⟨45, 1, 3, 7⟩ cache_45, place ⟨106, 6, 2, 3⟩ cache_106, place ⟨420, 1, 6, 4⟩ cache_420] = cache_427 := by
  decide +kernel

theorem load_entry_427 : entryAt 427 = entry_427 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_427 : CacheEquation 427 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(427 < 6)), load_entry_427]
  change forkRow [placeRow ⟨45, 1, 3, 7⟩ (denote cache_45), placeRow ⟨106, 6, 2, 3⟩ (denote cache_106), placeRow ⟨420, 1, 6, 4⟩ (denote cache_420)] = denote cache_427
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_427

theorem verified_row_428 : fork [place ⟨26, 3, 4, 3⟩ cache_26, place ⟨416, 0, 5, 4⟩ cache_416, place ⟨244, 0, 5, 4⟩ cache_244, place ⟨329, 0, 4, 3⟩ cache_329] = cache_428 := by
  decide +kernel

theorem load_entry_428 : entryAt 428 = entry_428 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_428 : CacheEquation 428 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(428 < 6)), load_entry_428]
  change forkRow [placeRow ⟨26, 3, 4, 3⟩ (denote cache_26), placeRow ⟨416, 0, 5, 4⟩ (denote cache_416), placeRow ⟨244, 0, 5, 4⟩ (denote cache_244), placeRow ⟨329, 0, 4, 3⟩ (denote cache_329)] = denote cache_428
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_428

theorem verified_row_429 : fork [place ⟨128, 0, 6, 3⟩ cache_128, place ⟨28, 3, 4, 5⟩ cache_28] = cache_429 := by
  decide +kernel

theorem load_entry_429 : entryAt 429 = entry_429 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_429 : CacheEquation 429 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(429 < 6)), load_entry_429]
  change forkRow [placeRow ⟨128, 0, 6, 3⟩ (denote cache_128), placeRow ⟨28, 3, 4, 5⟩ (denote cache_28)] = denote cache_429
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_429

theorem verified_row_430 : fork [place ⟨277, 7, 1, 3⟩ cache_277, place ⟨338, 4, 3, 4⟩ cache_338, place ⟨336, 1, 4, 3⟩ cache_336, place ⟨375, 2, 4, 3⟩ cache_375, place ⟨277, 6, 3, 1⟩ cache_277] = cache_430 := by
  decide +kernel

theorem load_entry_430 : entryAt 430 = entry_430 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_430 : CacheEquation 430 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(430 < 6)), load_entry_430]
  change forkRow [placeRow ⟨277, 7, 1, 3⟩ (denote cache_277), placeRow ⟨338, 4, 3, 4⟩ (denote cache_338), placeRow ⟨336, 1, 4, 3⟩ (denote cache_336), placeRow ⟨375, 2, 4, 3⟩ (denote cache_375), placeRow ⟨277, 6, 3, 1⟩ (denote cache_277)] = denote cache_430
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_430

theorem verified_row_431 : fork [place ⟨73, 4, 3, 3⟩ cache_73, place ⟨302, 1, 5, 2⟩ cache_302, place ⟨415, 0, 6, 4⟩ cache_415, place ⟨398, 0, 6, 4⟩ cache_398] = cache_431 := by
  decide +kernel

theorem load_entry_431 : entryAt 431 = entry_431 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_431 : CacheEquation 431 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(431 < 6)), load_entry_431]
  change forkRow [placeRow ⟨73, 4, 3, 3⟩ (denote cache_73), placeRow ⟨302, 1, 5, 2⟩ (denote cache_302), placeRow ⟨415, 0, 6, 4⟩ (denote cache_415), placeRow ⟨398, 0, 6, 4⟩ (denote cache_398)] = denote cache_431
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_431

theorem verified_row_432 : fork [place ⟨42, 3, 4, 3⟩ cache_42, place ⟨428, 0, 5, 4⟩ cache_428, place ⟨274, 0, 4, 3⟩ cache_274] = cache_432 := by
  decide +kernel

theorem load_entry_432 : entryAt 432 = entry_432 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_432 : CacheEquation 432 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(432 < 6)), load_entry_432]
  change forkRow [placeRow ⟨42, 3, 4, 3⟩ (denote cache_42), placeRow ⟨428, 0, 5, 4⟩ (denote cache_428), placeRow ⟨274, 0, 4, 3⟩ (denote cache_274)] = denote cache_432
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_432

theorem verified_row_433 : fork [place ⟨63, 0, 3, 5⟩ cache_63, place ⟨7, 3, 3, 4⟩ cache_7, place ⟨427, 0, 5, 2⟩ cache_427, place ⟨422, 0, 5, 2⟩ cache_422] = cache_433 := by
  decide +kernel

theorem load_entry_433 : entryAt 433 = entry_433 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_433 : CacheEquation 433 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(433 < 6)), load_entry_433]
  change forkRow [placeRow ⟨63, 0, 3, 5⟩ (denote cache_63), placeRow ⟨7, 3, 3, 4⟩ (denote cache_7), placeRow ⟨427, 0, 5, 2⟩ (denote cache_427), placeRow ⟨422, 0, 5, 2⟩ (denote cache_422)] = denote cache_433
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_433

theorem verified_row_434 : fork [place ⟨418, 0, 4, 5⟩ cache_418, place ⟨263, 2, 5, 4⟩ cache_263, place ⟨295, 0, 5, 4⟩ cache_295, place ⟨176, 2, 5, 4⟩ cache_176, place ⟨116, 0, 4, 3⟩ cache_116] = cache_434 := by
  decide +kernel

theorem load_entry_434 : entryAt 434 = entry_434 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_434 : CacheEquation 434 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(434 < 6)), load_entry_434]
  change forkRow [placeRow ⟨418, 0, 4, 5⟩ (denote cache_418), placeRow ⟨263, 2, 5, 4⟩ (denote cache_263), placeRow ⟨295, 0, 5, 4⟩ (denote cache_295), placeRow ⟨176, 2, 5, 4⟩ (denote cache_176), placeRow ⟨116, 0, 4, 3⟩ (denote cache_116)] = denote cache_434
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_434

theorem verified_row_435 : fork [place ⟨6, 4, 3, 4⟩ cache_6, place ⟨431, 0, 5, 6⟩ cache_431] = cache_435 := by
  decide +kernel

theorem load_entry_435 : entryAt 435 = entry_435 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_435 : CacheEquation 435 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(435 < 6)), load_entry_435]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (denote cache_6), placeRow ⟨431, 0, 5, 6⟩ (denote cache_431)] = denote cache_435
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_435

theorem verified_row_436 : fork [place ⟨51, 1, 5, 4⟩ cache_51, place ⟨60, 3, 4, 3⟩ cache_60, place ⟨274, 4, 4, 3⟩ cache_274, place ⟨428, 0, 5, 4⟩ cache_428] = cache_436 := by
  decide +kernel

theorem load_entry_436 : entryAt 436 = entry_436 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_436 : CacheEquation 436 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(436 < 6)), load_entry_436]
  change forkRow [placeRow ⟨51, 1, 5, 4⟩ (denote cache_51), placeRow ⟨60, 3, 4, 3⟩ (denote cache_60), placeRow ⟨274, 4, 4, 3⟩ (denote cache_274), placeRow ⟨428, 0, 5, 4⟩ (denote cache_428)] = denote cache_436
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_436

theorem verified_row_437 : fork [place ⟨55, 7, 4, 0⟩ cache_55, place ⟨427, 0, 5, 2⟩ cache_427, place ⟨63, 0, 3, 5⟩ cache_63, place ⟨422, 0, 5, 2⟩ cache_422] = cache_437 := by
  decide +kernel

theorem load_entry_437 : entryAt 437 = entry_437 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_437 : CacheEquation 437 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(437 < 6)), load_entry_437]
  change forkRow [placeRow ⟨55, 7, 4, 0⟩ (denote cache_55), placeRow ⟨427, 0, 5, 2⟩ (denote cache_427), placeRow ⟨63, 0, 3, 5⟩ (denote cache_63), placeRow ⟨422, 0, 5, 2⟩ (denote cache_422)] = denote cache_437
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_437

theorem verified_row_438 : fork [place ⟨0, 0, 1, 3⟩ cache_0, place ⟨432, 0, 4, 6⟩ cache_432] = cache_438 := by
  decide +kernel

theorem load_entry_438 : entryAt 438 = entry_438 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_438 : CacheEquation 438 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(438 < 6)), load_entry_438]
  change forkRow [placeRow ⟨0, 0, 1, 3⟩ (denote cache_0), placeRow ⟨432, 0, 4, 6⟩ (denote cache_432)] = denote cache_438
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_438

theorem verified_row_439 : fork [place ⟨176, 2, 5, 4⟩ cache_176, place ⟨295, 0, 5, 4⟩ cache_295, place ⟨263, 2, 5, 4⟩ cache_263, place ⟨418, 0, 4, 5⟩ cache_418, place ⟨149, 0, 4, 3⟩ cache_149] = cache_439 := by
  decide +kernel

theorem load_entry_439 : entryAt 439 = entry_439 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_439 : CacheEquation 439 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(439 < 6)), load_entry_439]
  change forkRow [placeRow ⟨176, 2, 5, 4⟩ (denote cache_176), placeRow ⟨295, 0, 5, 4⟩ (denote cache_295), placeRow ⟨263, 2, 5, 4⟩ (denote cache_263), placeRow ⟨418, 0, 4, 5⟩ (denote cache_418), placeRow ⟨149, 0, 4, 3⟩ (denote cache_149)] = denote cache_439
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_439

end SnakyCertificate.Check

end OAI
