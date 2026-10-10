import OAI.Combinatorics.SnakyCertificate.Cache
import OAI.Combinatorics.SnakyCertificate.TableList

namespace OAI

namespace SnakyCertificate.Check

theorem verified_row_480 : fork [place ⟨108, 1, 4, 5⟩ cache_108, place ⟨4, 1, 5, 4⟩ cache_4] = cache_480 := by
  decide +kernel

theorem load_entry_480 : entryAt 480 = entry_480 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_480 : CacheEquation 480 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(480 < 6)), load_entry_480]
  change forkRow [placeRow ⟨108, 1, 4, 5⟩ (denote cache_108), placeRow ⟨4, 1, 5, 4⟩ (denote cache_4)] = denote cache_480
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_480

theorem verified_row_481 : fork [place ⟨303, 1, 5, 4⟩ cache_303, place ⟨429, 2, 1, 4⟩ cache_429, place ⟨309, 1, 1, 4⟩ cache_309, place ⟨206, 2, 1, 4⟩ cache_206, place ⟨169, 2, 1, 4⟩ cache_169, place ⟨207, 2, 1, 4⟩ cache_207] = cache_481 := by
  decide +kernel

theorem load_entry_481 : entryAt 481 = entry_481 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_481 : CacheEquation 481 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(481 < 6)), load_entry_481]
  change forkRow [placeRow ⟨303, 1, 5, 4⟩ (denote cache_303), placeRow ⟨429, 2, 1, 4⟩ (denote cache_429), placeRow ⟨309, 1, 1, 4⟩ (denote cache_309), placeRow ⟨206, 2, 1, 4⟩ (denote cache_206), placeRow ⟨169, 2, 1, 4⟩ (denote cache_169), placeRow ⟨207, 2, 1, 4⟩ (denote cache_207)] = denote cache_481
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_481

theorem verified_row_482 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨218, 2, 4, 3⟩ cache_218] = cache_482 := by
  decide +kernel

theorem load_entry_482 : entryAt 482 = entry_482 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_482 : CacheEquation 482 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(482 < 6)), load_entry_482]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨218, 2, 4, 3⟩ (denote cache_218)] = denote cache_482
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_482

theorem verified_row_483 : fork [place ⟨173, 1, 4, 5⟩ cache_173, place ⟨292, 7, 3, 1⟩ cache_292, place ⟨319, 1, 3, 5⟩ cache_319, place ⟨192, 6, 4, 1⟩ cache_192, place ⟨475, 1, 4, 5⟩ cache_475] = cache_483 := by
  decide +kernel

theorem load_entry_483 : entryAt 483 = entry_483 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_483 : CacheEquation 483 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(483 < 6)), load_entry_483]
  change forkRow [placeRow ⟨173, 1, 4, 5⟩ (denote cache_173), placeRow ⟨292, 7, 3, 1⟩ (denote cache_292), placeRow ⟨319, 1, 3, 5⟩ (denote cache_319), placeRow ⟨192, 6, 4, 1⟩ (denote cache_192), placeRow ⟨475, 1, 4, 5⟩ (denote cache_475)] = denote cache_483
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_483

theorem verified_row_484 : fork [place ⟨25, 4, 1, 5⟩ cache_25, place ⟨107, 2, 5, 4⟩ cache_107, place ⟨349, 3, 1, 5⟩ cache_349, place ⟨163, 2, 5, 4⟩ cache_163] = cache_484 := by
  decide +kernel

theorem load_entry_484 : entryAt 484 = entry_484 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_484 : CacheEquation 484 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(484 < 6)), load_entry_484]
  change forkRow [placeRow ⟨25, 4, 1, 5⟩ (denote cache_25), placeRow ⟨107, 2, 5, 4⟩ (denote cache_107), placeRow ⟨349, 3, 1, 5⟩ (denote cache_349), placeRow ⟨163, 2, 5, 4⟩ (denote cache_163)] = denote cache_484
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_484

theorem verified_row_485 : fork [place ⟨484, 0, 5, 4⟩ cache_484, place ⟨2, 3, 4, 3⟩ cache_2] = cache_485 := by
  decide +kernel

theorem load_entry_485 : entryAt 485 = entry_485 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_485 : CacheEquation 485 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(485 < 6)), load_entry_485]
  change forkRow [placeRow ⟨484, 0, 5, 4⟩ (denote cache_484), placeRow ⟨2, 3, 4, 3⟩ (denote cache_2)] = denote cache_485
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_485

theorem verified_row_486 : fork [place ⟨2, 5, 4, 2⟩ cache_2, place ⟨485, 0, 5, 3⟩ cache_485] = cache_486 := by
  decide +kernel

theorem load_entry_486 : entryAt 486 = entry_486 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_486 : CacheEquation 486 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(486 < 6)), load_entry_486]
  change forkRow [placeRow ⟨2, 5, 4, 2⟩ (denote cache_2), placeRow ⟨485, 0, 5, 3⟩ (denote cache_485)] = denote cache_486
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_486

theorem verified_row_487 : fork [place ⟨2, 3, 4, 3⟩ cache_2, place ⟨481, 0, 5, 4⟩ cache_481] = cache_487 := by
  decide +kernel

theorem load_entry_487 : entryAt 487 = entry_487 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_487 : CacheEquation 487 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(487 < 6)), load_entry_487]
  change forkRow [placeRow ⟨2, 3, 4, 3⟩ (denote cache_2), placeRow ⟨481, 0, 5, 4⟩ (denote cache_481)] = denote cache_487
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_487

theorem verified_row_488 : fork [place ⟨0, 6, 6, 4⟩ cache_0, place ⟨247, 0, 2, 5⟩ cache_247] = cache_488 := by
  decide +kernel

theorem load_entry_488 : entryAt 488 = entry_488 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_488 : CacheEquation 488 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(488 < 6)), load_entry_488]
  change forkRow [placeRow ⟨0, 6, 6, 4⟩ (denote cache_0), placeRow ⟨247, 0, 2, 5⟩ (denote cache_247)] = denote cache_488
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_488

theorem verified_row_489 : fork [place ⟨356, 1, 3, 3⟩ cache_356, place ⟨197, 4, 1, 4⟩ cache_197, place ⟨172, 6, 1, 4⟩ cache_172] = cache_489 := by
  decide +kernel

theorem load_entry_489 : entryAt 489 = entry_489 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_489 : CacheEquation 489 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(489 < 6)), load_entry_489]
  change forkRow [placeRow ⟨356, 1, 3, 3⟩ (denote cache_356), placeRow ⟨197, 4, 1, 4⟩ (denote cache_197), placeRow ⟨172, 6, 1, 4⟩ (denote cache_172)] = denote cache_489
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_489

theorem verified_row_490 : fork [place ⟨64, 1, 3, 1⟩ cache_64, place ⟨471, 0, 5, 1⟩ cache_471, place ⟨470, 1, 5, 1⟩ cache_470, place ⟨111, 0, 3, 1⟩ cache_111] = cache_490 := by
  decide +kernel

theorem load_entry_490 : entryAt 490 = entry_490 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_490 : CacheEquation 490 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(490 < 6)), load_entry_490]
  change forkRow [placeRow ⟨64, 1, 3, 1⟩ (denote cache_64), placeRow ⟨471, 0, 5, 1⟩ (denote cache_471), placeRow ⟨470, 1, 5, 1⟩ (denote cache_470), placeRow ⟨111, 0, 3, 1⟩ (denote cache_111)] = denote cache_490
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_490

theorem verified_row_491 : fork [place ⟨6, 3, 3, 5⟩ cache_6, place ⟨273, 0, 5, 4⟩ cache_273] = cache_491 := by
  decide +kernel

theorem load_entry_491 : entryAt 491 = entry_491 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_491 : CacheEquation 491 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(491 < 6)), load_entry_491]
  change forkRow [placeRow ⟨6, 3, 3, 5⟩ (denote cache_6), placeRow ⟨273, 0, 5, 4⟩ (denote cache_273)] = denote cache_491
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_491

theorem verified_row_492 : fork [place ⟨62, 4, 3, 4⟩ cache_62, place ⟨107, 4, 3, 4⟩ cache_107, place ⟨487, 0, 6, 6⟩ cache_487] = cache_492 := by
  decide +kernel

theorem load_entry_492 : entryAt 492 = entry_492 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_492 : CacheEquation 492 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(492 < 6)), load_entry_492]
  change forkRow [placeRow ⟨62, 4, 3, 4⟩ (denote cache_62), placeRow ⟨107, 4, 3, 4⟩ (denote cache_107), placeRow ⟨487, 0, 6, 6⟩ (denote cache_487)] = denote cache_492
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_492

theorem verified_row_493 : fork [place ⟨225, 0, 1, 4⟩ cache_225, place ⟨455, 0, 5, 3⟩ cache_455, place ⟨236, 1, 5, 5⟩ cache_236, place ⟨221, 0, 5, 4⟩ cache_221] = cache_493 := by
  decide +kernel

theorem load_entry_493 : entryAt 493 = entry_493 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_493 : CacheEquation 493 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(493 < 6)), load_entry_493]
  change forkRow [placeRow ⟨225, 0, 1, 4⟩ (denote cache_225), placeRow ⟨455, 0, 5, 3⟩ (denote cache_455), placeRow ⟨236, 1, 5, 5⟩ (denote cache_236), placeRow ⟨221, 0, 5, 4⟩ (denote cache_221)] = denote cache_493
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_493

theorem verified_row_494 : fork [place ⟨297, 4, 4, 5⟩ cache_297, place ⟨268, 4, 1, 5⟩ cache_268, place ⟨162, 5, 5, 4⟩ cache_162] = cache_494 := by
  decide +kernel

theorem load_entry_494 : entryAt 494 = entry_494 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_494 : CacheEquation 494 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(494 < 6)), load_entry_494]
  change forkRow [placeRow ⟨297, 4, 4, 5⟩ (denote cache_297), placeRow ⟨268, 4, 1, 5⟩ (denote cache_268), placeRow ⟨162, 5, 5, 4⟩ (denote cache_162)] = denote cache_494
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_494

theorem verified_row_495 : fork [place ⟨25, 6, 1, 3⟩ cache_25, place ⟨167, 4, 1, 4⟩ cache_167, place ⟨456, 4, 1, 4⟩ cache_456] = cache_495 := by
  decide +kernel

theorem load_entry_495 : entryAt 495 = entry_495 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_495 : CacheEquation 495 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(495 < 6)), load_entry_495]
  change forkRow [placeRow ⟨25, 6, 1, 3⟩ (denote cache_25), placeRow ⟨167, 4, 1, 4⟩ (denote cache_167), placeRow ⟨456, 4, 1, 4⟩ (denote cache_456)] = denote cache_495
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_495

theorem verified_row_496 : fork [place ⟨25, 0, 7, 5⟩ cache_25, place ⟨107, 6, 3, 4⟩ cache_107, place ⟨163, 6, 3, 4⟩ cache_163, place ⟨494, 0, 7, 4⟩ cache_494] = cache_496 := by
  decide +kernel

theorem load_entry_496 : entryAt 496 = entry_496 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_496 : CacheEquation 496 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(496 < 6)), load_entry_496]
  change forkRow [placeRow ⟨25, 0, 7, 5⟩ (denote cache_25), placeRow ⟨107, 6, 3, 4⟩ (denote cache_107), placeRow ⟨163, 6, 3, 4⟩ (denote cache_163), placeRow ⟨494, 0, 7, 4⟩ (denote cache_494)] = denote cache_496
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_496

theorem verified_row_497 : fork [place ⟨36, 2, 3, 4⟩ cache_36, place ⟨167, 0, 7, 4⟩ cache_167, place ⟨410, 0, 7, 3⟩ cache_410] = cache_497 := by
  decide +kernel

theorem load_entry_497 : entryAt 497 = entry_497 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_497 : CacheEquation 497 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(497 < 6)), load_entry_497]
  change forkRow [placeRow ⟨36, 2, 3, 4⟩ (denote cache_36), placeRow ⟨167, 0, 7, 4⟩ (denote cache_167), placeRow ⟨410, 0, 7, 3⟩ (denote cache_410)] = denote cache_497
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_497

theorem verified_row_498 : fork [place ⟨14, 1, 4, 6⟩ cache_14, place ⟨298, 2, 2, 4⟩ cache_298] = cache_498 := by
  decide +kernel

theorem load_entry_498 : entryAt 498 = entry_498 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_498 : CacheEquation 498 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(498 < 6)), load_entry_498]
  change forkRow [placeRow ⟨14, 1, 4, 6⟩ (denote cache_14), placeRow ⟨298, 2, 2, 4⟩ (denote cache_298)] = denote cache_498
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_498

theorem verified_row_499 : fork [place ⟨493, 0, 5, 4⟩ cache_493, place ⟨25, 1, 4, 5⟩ cache_25, place ⟨478, 0, 2, 4⟩ cache_478] = cache_499 := by
  decide +kernel

theorem load_entry_499 : entryAt 499 = entry_499 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_499 : CacheEquation 499 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(499 < 6)), load_entry_499]
  change forkRow [placeRow ⟨493, 0, 5, 4⟩ (denote cache_493), placeRow ⟨25, 1, 4, 5⟩ (denote cache_25), placeRow ⟨478, 0, 2, 4⟩ (denote cache_478)] = denote cache_499
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_499

theorem verified_row_500 : fork [place ⟨1, 5, 3, 6⟩ cache_1, place ⟨351, 0, 5, 4⟩ cache_351] = cache_500 := by
  decide +kernel

theorem load_entry_500 : entryAt 500 = entry_500 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_500 : CacheEquation 500 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(500 < 6)), load_entry_500]
  change forkRow [placeRow ⟨1, 5, 3, 6⟩ (denote cache_1), placeRow ⟨351, 0, 5, 4⟩ (denote cache_351)] = denote cache_500
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_500

theorem verified_row_501 : fork [place ⟨6, 4, 0, 5⟩ cache_6, place ⟨316, 0, 1, 3⟩ cache_316] = cache_501 := by
  decide +kernel

theorem load_entry_501 : entryAt 501 = entry_501 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_501 : CacheEquation 501 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(501 < 6)), load_entry_501]
  change forkRow [placeRow ⟨6, 4, 0, 5⟩ (denote cache_6), placeRow ⟨316, 0, 1, 3⟩ (denote cache_316)] = denote cache_501
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_501

theorem verified_row_502 : fork [place ⟨215, 6, 2, 3⟩ cache_215, place ⟨232, 0, 4, 3⟩ cache_232, place ⟨192, 7, 1, 4⟩ cache_192, place ⟨173, 0, 5, 4⟩ cache_173, place ⟨271, 2, 2, 3⟩ cache_271] = cache_502 := by
  decide +kernel

theorem load_entry_502 : entryAt 502 = entry_502 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_502 : CacheEquation 502 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(502 < 6)), load_entry_502]
  change forkRow [placeRow ⟨215, 6, 2, 3⟩ (denote cache_215), placeRow ⟨232, 0, 4, 3⟩ (denote cache_232), placeRow ⟨192, 7, 1, 4⟩ (denote cache_192), placeRow ⟨173, 0, 5, 4⟩ (denote cache_173), placeRow ⟨271, 2, 2, 3⟩ (denote cache_271)] = denote cache_502
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_502

theorem verified_row_503 : fork [place ⟨63, 0, 3, 5⟩ cache_63, place ⟨55, 7, 4, 0⟩ cache_55, place ⟨420, 1, 7, 2⟩ cache_420, place ⟨419, 1, 7, 4⟩ cache_419] = cache_503 := by
  decide +kernel

theorem load_entry_503 : entryAt 503 = entry_503 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_503 : CacheEquation 503 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(503 < 6)), load_entry_503]
  change forkRow [placeRow ⟨63, 0, 3, 5⟩ (denote cache_63), placeRow ⟨55, 7, 4, 0⟩ (denote cache_55), placeRow ⟨420, 1, 7, 2⟩ (denote cache_420), placeRow ⟨419, 1, 7, 4⟩ (denote cache_419)] = denote cache_503
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_503

theorem verified_row_504 : fork [place ⟨381, 0, 3, 4⟩ cache_381, place ⟨310, 4, 4, 5⟩ cache_310, place ⟨159, 0, 5, 6⟩ cache_159, place ⟨351, 4, 3, 4⟩ cache_351, place ⟨496, 0, 3, 4⟩ cache_496] = cache_504 := by
  decide +kernel

theorem load_entry_504 : entryAt 504 = entry_504 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_504 : CacheEquation 504 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(504 < 6)), load_entry_504]
  change forkRow [placeRow ⟨381, 0, 3, 4⟩ (denote cache_381), placeRow ⟨310, 4, 4, 5⟩ (denote cache_310), placeRow ⟨159, 0, 5, 6⟩ (denote cache_159), placeRow ⟨351, 4, 3, 4⟩ (denote cache_351), placeRow ⟨496, 0, 3, 4⟩ (denote cache_496)] = denote cache_504
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_504

theorem verified_row_505 : fork [place ⟨173, 1, 4, 5⟩ cache_173, place ⟨499, 0, 5, 4⟩ cache_499, place ⟨183, 1, 4, 5⟩ cache_183, place ⟨282, 1, 4, 5⟩ cache_282] = cache_505 := by
  decide +kernel

theorem load_entry_505 : entryAt 505 = entry_505 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_505 : CacheEquation 505 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(505 < 6)), load_entry_505]
  change forkRow [placeRow ⟨173, 1, 4, 5⟩ (denote cache_173), placeRow ⟨499, 0, 5, 4⟩ (denote cache_499), placeRow ⟨183, 1, 4, 5⟩ (denote cache_183), placeRow ⟨282, 1, 4, 5⟩ (denote cache_282)] = denote cache_505
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_505

theorem verified_row_506 : fork [place ⟨99, 0, 4, 5⟩ cache_99, place ⟨200, 7, 1, 4⟩ cache_200, place ⟨318, 5, 5, 4⟩ cache_318, place ⟨173, 0, 5, 4⟩ cache_173] = cache_506 := by
  decide +kernel

theorem load_entry_506 : entryAt 506 = entry_506 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_506 : CacheEquation 506 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(506 < 6)), load_entry_506]
  change forkRow [placeRow ⟨99, 0, 4, 5⟩ (denote cache_99), placeRow ⟨200, 7, 1, 4⟩ (denote cache_200), placeRow ⟨318, 5, 5, 4⟩ (denote cache_318), placeRow ⟨173, 0, 5, 4⟩ (denote cache_173)] = denote cache_506
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_506

theorem verified_row_507 : fork [place ⟨151, 0, 2, 4⟩ cache_151, place ⟨33, 3, 4, 3⟩ cache_33, place ⟨481, 0, 5, 4⟩ cache_481] = cache_507 := by
  decide +kernel

theorem load_entry_507 : entryAt 507 = entry_507 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_507 : CacheEquation 507 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(507 < 6)), load_entry_507]
  change forkRow [placeRow ⟨151, 0, 2, 4⟩ (denote cache_151), placeRow ⟨33, 3, 4, 3⟩ (denote cache_33), placeRow ⟨481, 0, 5, 4⟩ (denote cache_481)] = denote cache_507
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_507

theorem verified_row_508 : fork [place ⟨6, 0, 5, 4⟩ cache_6, place ⟨393, 0, 1, 5⟩ cache_393] = cache_508 := by
  decide +kernel

theorem load_entry_508 : entryAt 508 = entry_508 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_508 : CacheEquation 508 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(508 < 6)), load_entry_508]
  change forkRow [placeRow ⟨6, 0, 5, 4⟩ (denote cache_6), placeRow ⟨393, 0, 1, 5⟩ (denote cache_393)] = denote cache_508
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_508

theorem verified_row_509 : fork [place ⟨252, 0, 6, 4⟩ cache_252, place ⟨241, 4, 2, 4⟩ cache_241, place ⟨455, 0, 6, 3⟩ cache_455, place ⟨68, 2, 6, 4⟩ cache_68] = cache_509 := by
  decide +kernel

theorem load_entry_509 : entryAt 509 = entry_509 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_509 : CacheEquation 509 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(509 < 6)), load_entry_509]
  change forkRow [placeRow ⟨252, 0, 6, 4⟩ (denote cache_252), placeRow ⟨241, 4, 2, 4⟩ (denote cache_241), placeRow ⟨455, 0, 6, 3⟩ (denote cache_455), placeRow ⟨68, 2, 6, 4⟩ (denote cache_68)] = denote cache_509
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_509

theorem verified_row_510 : fork [place ⟨6, 4, 3, 4⟩ cache_6, place ⟨508, 0, 7, 4⟩ cache_508] = cache_510 := by
  decide +kernel

theorem load_entry_510 : entryAt 510 = entry_510 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_510 : CacheEquation 510 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(510 < 6)), load_entry_510]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (denote cache_6), placeRow ⟨508, 0, 7, 4⟩ (denote cache_508)] = denote cache_510
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_510

theorem verified_row_511 : fork [place ⟨15, 1, 4, 5⟩ cache_15, place ⟨331, 0, 5, 3⟩ cache_331, place ⟨380, 4, 2, 4⟩ cache_380] = cache_511 := by
  decide +kernel

theorem load_entry_511 : entryAt 511 = entry_511 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_511 : CacheEquation 511 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(511 < 6)), load_entry_511]
  change forkRow [placeRow ⟨15, 1, 4, 5⟩ (denote cache_15), placeRow ⟨331, 0, 5, 3⟩ (denote cache_331), placeRow ⟨380, 4, 2, 4⟩ (denote cache_380)] = denote cache_511
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_511

theorem verified_row_512 : fork [place ⟨62, 0, 5, 4⟩ cache_62, place ⟨107, 0, 5, 4⟩ cache_107, place ⟨507, 0, 4, 6⟩ cache_507] = cache_512 := by
  decide +kernel

theorem load_entry_512 : entryAt 512 = entry_512 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_512 : CacheEquation 512 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(512 < 6)), load_entry_512]
  change forkRow [placeRow ⟨62, 0, 5, 4⟩ (denote cache_62), placeRow ⟨107, 0, 5, 4⟩ (denote cache_107), placeRow ⟨507, 0, 4, 6⟩ (denote cache_507)] = denote cache_512
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_512

theorem verified_row_513 : fork [place ⟨6, 4, 3, 4⟩ cache_6, place ⟨396, 0, 4, 5⟩ cache_396] = cache_513 := by
  decide +kernel

theorem load_entry_513 : entryAt 513 = entry_513 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_513 : CacheEquation 513 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(513 < 6)), load_entry_513]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (denote cache_6), placeRow ⟨396, 0, 4, 5⟩ (denote cache_396)] = denote cache_513
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_513

theorem verified_row_514 : fork [place ⟨57, 0, 5, 4⟩ cache_57, place ⟨443, 4, 1, 5⟩ cache_443, place ⟨510, 0, 1, 5⟩ cache_510] = cache_514 := by
  decide +kernel

theorem load_entry_514 : entryAt 514 = entry_514 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_514 : CacheEquation 514 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(514 < 6)), load_entry_514]
  change forkRow [placeRow ⟨57, 0, 5, 4⟩ (denote cache_57), placeRow ⟨443, 4, 1, 5⟩ (denote cache_443), placeRow ⟨510, 0, 1, 5⟩ (denote cache_510)] = denote cache_514
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_514

theorem verified_row_515 : fork [place ⟨2, 6, 2, 4⟩ cache_2, place ⟨512, 1, 1, 5⟩ cache_512] = cache_515 := by
  decide +kernel

theorem load_entry_515 : entryAt 515 = entry_515 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_515 : CacheEquation 515 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(515 < 6)), load_entry_515]
  change forkRow [placeRow ⟨2, 6, 2, 4⟩ (denote cache_2), placeRow ⟨512, 1, 1, 5⟩ (denote cache_512)] = denote cache_515
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_515

theorem verified_row_516 : fork [place ⟨329, 0, 4, 3⟩ cache_329, place ⟨244, 4, 2, 4⟩ cache_244, place ⟨10, 1, 4, 5⟩ cache_10, place ⟨506, 4, 2, 4⟩ cache_506] = cache_516 := by
  decide +kernel

theorem load_entry_516 : entryAt 516 = entry_516 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_516 : CacheEquation 516 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(516 < 6)), load_entry_516]
  change forkRow [placeRow ⟨329, 0, 4, 3⟩ (denote cache_329), placeRow ⟨244, 4, 2, 4⟩ (denote cache_244), placeRow ⟨10, 1, 4, 5⟩ (denote cache_10), placeRow ⟨506, 4, 2, 4⟩ (denote cache_506)] = denote cache_516
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_516

theorem verified_row_517 : fork [place ⟨496, 0, 2, 3⟩ cache_496, place ⟨140, 0, 4, 2⟩ cache_140, place ⟨193, 1, 4, 2⟩ cache_193] = cache_517 := by
  decide +kernel

theorem load_entry_517 : entryAt 517 = entry_517 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_517 : CacheEquation 517 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(517 < 6)), load_entry_517]
  change forkRow [placeRow ⟨496, 0, 2, 3⟩ (denote cache_496), placeRow ⟨140, 0, 4, 2⟩ (denote cache_140), placeRow ⟨193, 1, 4, 2⟩ (denote cache_193)] = denote cache_517
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_517

theorem verified_row_518 : fork [place ⟨9, 6, 3, 4⟩ cache_9, place ⟨514, 0, 7, 4⟩ cache_514] = cache_518 := by
  decide +kernel

theorem load_entry_518 : entryAt 518 = entry_518 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_518 : CacheEquation 518 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(518 < 6)), load_entry_518]
  change forkRow [placeRow ⟨9, 6, 3, 4⟩ (denote cache_9), placeRow ⟨514, 0, 7, 4⟩ (denote cache_514)] = denote cache_518
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_518

theorem verified_row_519 : fork [place ⟨498, 0, 4, 3⟩ cache_498, place ⟨311, 4, 3, 4⟩ cache_311, place ⟨38, 1, 4, 5⟩ cache_38, place ⟨408, 0, 3, 4⟩ cache_408] = cache_519 := by
  decide +kernel

theorem load_entry_519 : entryAt 519 = entry_519 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_519 : CacheEquation 519 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(519 < 6)), load_entry_519]
  change forkRow [placeRow ⟨498, 0, 4, 3⟩ (denote cache_498), placeRow ⟨311, 4, 3, 4⟩ (denote cache_311), placeRow ⟨38, 1, 4, 5⟩ (denote cache_38), placeRow ⟨408, 0, 3, 4⟩ (denote cache_408)] = denote cache_519
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_519

end SnakyCertificate.Check

end OAI
