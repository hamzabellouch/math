import OAI.Combinatorics.SnakyCertificate.Cache
import OAI.Combinatorics.SnakyCertificate.TableList

namespace OAI

namespace SnakyCertificate.Check

theorem verified_row_520 : fork [place ⟨254, 0, 2, 3⟩ cache_254, place ⟨200, 5, 6, 4⟩ cache_200, place ⟨271, 6, 5, 3⟩ cache_271, place ⟨215, 2, 5, 3⟩ cache_215, place ⟨252, 4, 2, 4⟩ cache_252] = cache_520 := by
  decide +kernel

theorem load_entry_520 : entryAt 520 = entry_520 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_520 : CacheEquation 520 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(520 < 6)), load_entry_520]
  change forkRow [placeRow ⟨254, 0, 2, 3⟩ (denote cache_254), placeRow ⟨200, 5, 6, 4⟩ (denote cache_200), placeRow ⟨271, 6, 5, 3⟩ (denote cache_271), placeRow ⟨215, 2, 5, 3⟩ (denote cache_215), placeRow ⟨252, 4, 2, 4⟩ (denote cache_252)] = denote cache_520
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_520

theorem verified_row_521 : fork [place ⟨492, 4, 5, 1⟩ cache_492, place ⟨2, 7, 4, 2⟩ cache_2] = cache_521 := by
  decide +kernel

theorem load_entry_521 : entryAt 521 = entry_521 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_521 : CacheEquation 521 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(521 < 6)), load_entry_521]
  change forkRow [placeRow ⟨492, 4, 5, 1⟩ (denote cache_492), placeRow ⟨2, 7, 4, 2⟩ (denote cache_2)] = denote cache_521
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_521

theorem verified_row_522 : fork [place ⟨176, 3, 4, 6⟩ cache_176, place ⟨338, 2, 3, 3⟩ cache_338, place ⟨252, 1, 4, 6⟩ cache_252] = cache_522 := by
  decide +kernel

theorem load_entry_522 : entryAt 522 = entry_522 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_522 : CacheEquation 522 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(522 < 6)), load_entry_522]
  change forkRow [placeRow ⟨176, 3, 4, 6⟩ (denote cache_176), placeRow ⟨338, 2, 3, 3⟩ (denote cache_338), placeRow ⟨252, 1, 4, 6⟩ (denote cache_252)] = denote cache_522
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_522

theorem verified_row_523 : fork [place ⟨303, 1, 5, 4⟩ cache_303, place ⟨25, 4, 1, 5⟩ cache_25, place ⟨107, 2, 5, 4⟩ cache_107, place ⟨511, 4, 1, 6⟩ cache_511] = cache_523 := by
  decide +kernel

theorem load_entry_523 : entryAt 523 = entry_523 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_523 : CacheEquation 523 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(523 < 6)), load_entry_523]
  change forkRow [placeRow ⟨303, 1, 5, 4⟩ (denote cache_303), placeRow ⟨25, 4, 1, 5⟩ (denote cache_25), placeRow ⟨107, 2, 5, 4⟩ (denote cache_107), placeRow ⟨511, 4, 1, 6⟩ (denote cache_511)] = denote cache_523
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_523

theorem verified_row_524 : fork [place ⟨504, 4, 5, 3⟩ cache_504, place ⟨504, 0, 3, 3⟩ cache_504, place ⟨180, 0, 4, 5⟩ cache_180, place ⟨180, 4, 4, 5⟩ cache_180, place ⟨261, 0, 3, 4⟩ cache_261] = cache_524 := by
  decide +kernel

theorem load_entry_524 : entryAt 524 = entry_524 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_524 : CacheEquation 524 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(524 < 6)), load_entry_524]
  change forkRow [placeRow ⟨504, 4, 5, 3⟩ (denote cache_504), placeRow ⟨504, 0, 3, 3⟩ (denote cache_504), placeRow ⟨180, 0, 4, 5⟩ (denote cache_180), placeRow ⟨180, 4, 4, 5⟩ (denote cache_180), placeRow ⟨261, 0, 3, 4⟩ (denote cache_261)] = denote cache_524
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_524

theorem verified_row_525 : fork [place ⟨303, 1, 5, 4⟩ cache_303, place ⟨25, 4, 1, 5⟩ cache_25, place ⟨430, 0, 4, 6⟩ cache_430, place ⟨107, 2, 5, 4⟩ cache_107] = cache_525 := by
  decide +kernel

theorem load_entry_525 : entryAt 525 = entry_525 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_525 : CacheEquation 525 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(525 < 6)), load_entry_525]
  change forkRow [placeRow ⟨303, 1, 5, 4⟩ (denote cache_303), placeRow ⟨25, 4, 1, 5⟩ (denote cache_25), placeRow ⟨430, 0, 4, 6⟩ (denote cache_430), placeRow ⟨107, 2, 5, 4⟩ (denote cache_107)] = denote cache_525
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_525

theorem verified_row_526 : fork [place ⟨359, 0, 4, 3⟩ cache_359, place ⟨416, 4, 2, 4⟩ cache_416, place ⟨327, 5, 4, 3⟩ cache_327, place ⟨489, 0, 5, 4⟩ cache_489, place ⟨399, 3, 2, 4⟩ cache_399] = cache_526 := by
  decide +kernel

theorem load_entry_526 : entryAt 526 = entry_526 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_526 : CacheEquation 526 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(526 < 6)), load_entry_526]
  change forkRow [placeRow ⟨359, 0, 4, 3⟩ (denote cache_359), placeRow ⟨416, 4, 2, 4⟩ (denote cache_416), placeRow ⟨327, 5, 4, 3⟩ (denote cache_327), placeRow ⟨489, 0, 5, 4⟩ (denote cache_489), placeRow ⟨399, 3, 2, 4⟩ (denote cache_399)] = denote cache_526
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_526

theorem verified_row_527 : fork [place ⟨387, 4, 4, 3⟩ cache_387, place ⟨38, 3, 4, 5⟩ cache_38, place ⟨491, 0, 5, 4⟩ cache_491, place ⟨519, 0, 6, 4⟩ cache_519] = cache_527 := by
  decide +kernel

theorem load_entry_527 : entryAt 527 = entry_527 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_527 : CacheEquation 527 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(527 < 6)), load_entry_527]
  change forkRow [placeRow ⟨387, 4, 4, 3⟩ (denote cache_387), placeRow ⟨38, 3, 4, 5⟩ (denote cache_38), placeRow ⟨491, 0, 5, 4⟩ (denote cache_491), placeRow ⟨519, 0, 6, 4⟩ (denote cache_519)] = denote cache_527
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_527

theorem verified_row_528 : fork [place ⟨414, 1, 3, 5⟩ cache_414, place ⟨386, 1, 4, 6⟩ cache_386, place ⟨502, 5, 4, 3⟩ cache_502, place ⟨226, 4, 1, 5⟩ cache_226, place ⟨359, 5, 3, 4⟩ cache_359] = cache_528 := by
  decide +kernel

theorem load_entry_528 : entryAt 528 = entry_528 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_528 : CacheEquation 528 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(528 < 6)), load_entry_528]
  change forkRow [placeRow ⟨414, 1, 3, 5⟩ (denote cache_414), placeRow ⟨386, 1, 4, 6⟩ (denote cache_386), placeRow ⟨502, 5, 4, 3⟩ (denote cache_502), placeRow ⟨226, 4, 1, 5⟩ (denote cache_226), placeRow ⟨359, 5, 3, 4⟩ (denote cache_359)] = denote cache_528
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_528

theorem verified_row_529 : fork [place ⟨55, 4, 3, 4⟩ cache_55, place ⟨441, 0, 4, 3⟩ cache_441, place ⟨63, 3, 3, 3⟩ cache_63, place ⟨64, 6, 7, 5⟩ cache_64] = cache_529 := by
  decide +kernel

theorem load_entry_529 : entryAt 529 = entry_529 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_529 : CacheEquation 529 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(529 < 6)), load_entry_529]
  change forkRow [placeRow ⟨55, 4, 3, 4⟩ (denote cache_55), placeRow ⟨441, 0, 4, 3⟩ (denote cache_441), placeRow ⟨63, 3, 3, 3⟩ (denote cache_63), placeRow ⟨64, 6, 7, 5⟩ (denote cache_64)] = denote cache_529
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_529

theorem verified_row_530 : fork [place ⟨456, 7, 4, 2⟩ cache_456, place ⟨336, 0, 5, 5⟩ cache_336, place ⟨283, 7, 4, 2⟩ cache_283, place ⟨271, 5, 5, 5⟩ cache_271] = cache_530 := by
  decide +kernel

theorem load_entry_530 : entryAt 530 = entry_530 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_530 : CacheEquation 530 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(530 < 6)), load_entry_530]
  change forkRow [placeRow ⟨456, 7, 4, 2⟩ (denote cache_456), placeRow ⟨336, 0, 5, 5⟩ (denote cache_336), placeRow ⟨283, 7, 4, 2⟩ (denote cache_283), placeRow ⟨271, 5, 5, 5⟩ (denote cache_271)] = denote cache_530
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_530

theorem verified_row_531 : fork [place ⟨425, 0, 5, 4⟩ cache_425, place ⟨336, 3, 4, 3⟩ cache_336, place ⟨340, 6, 4, 3⟩ cache_340, place ⟨394, 1, 5, 4⟩ cache_394, place ⟨423, 0, 5, 4⟩ cache_423, place ⟨526, 0, 5, 4⟩ cache_526, place ⟨401, 4, 4, 3⟩ cache_401, place ⟨453, 0, 5, 4⟩ cache_453] = cache_531 := by
  decide +kernel

theorem load_entry_531 : entryAt 531 = entry_531 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_531 : CacheEquation 531 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(531 < 6)), load_entry_531]
  change forkRow [placeRow ⟨425, 0, 5, 4⟩ (denote cache_425), placeRow ⟨336, 3, 4, 3⟩ (denote cache_336), placeRow ⟨340, 6, 4, 3⟩ (denote cache_340), placeRow ⟨394, 1, 5, 4⟩ (denote cache_394), placeRow ⟨423, 0, 5, 4⟩ (denote cache_423), placeRow ⟨526, 0, 5, 4⟩ (denote cache_526), placeRow ⟨401, 4, 4, 3⟩ (denote cache_401), placeRow ⟨453, 0, 5, 4⟩ (denote cache_453)] = denote cache_531
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_531

theorem verified_row_532 : fork [place ⟨504, 4, 5, 3⟩ cache_504, place ⟨6, 7, 3, 0⟩ cache_6] = cache_532 := by
  decide +kernel

theorem load_entry_532 : entryAt 532 = entry_532 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_532 : CacheEquation 532 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(532 < 6)), load_entry_532]
  change forkRow [placeRow ⟨504, 4, 5, 3⟩ (denote cache_504), placeRow ⟨6, 7, 3, 0⟩ (denote cache_6)] = denote cache_532
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_532

theorem verified_row_533 : fork [place ⟨318, 4, 4, 5⟩ cache_318, place ⟨319, 7, 5, 1⟩ cache_319, place ⟨407, 4, 4, 1⟩ cache_407, place ⟨173, 3, 4, 5⟩ cache_173, place ⟨217, 1, 4, 5⟩ cache_217] = cache_533 := by
  decide +kernel

theorem load_entry_533 : entryAt 533 = entry_533 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_533 : CacheEquation 533 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(533 < 6)), load_entry_533]
  change forkRow [placeRow ⟨318, 4, 4, 5⟩ (denote cache_318), placeRow ⟨319, 7, 5, 1⟩ (denote cache_319), placeRow ⟨407, 4, 4, 1⟩ (denote cache_407), placeRow ⟨173, 3, 4, 5⟩ (denote cache_173), placeRow ⟨217, 1, 4, 5⟩ (denote cache_217)] = denote cache_533
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_533

theorem verified_row_534 : fork [place ⟨434, 0, 4, 6⟩ cache_434, place ⟨12, 6, 1, 3⟩ cache_12] = cache_534 := by
  decide +kernel

theorem load_entry_534 : entryAt 534 = entry_534 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_534 : CacheEquation 534 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(534 < 6)), load_entry_534]
  change forkRow [placeRow ⟨434, 0, 4, 6⟩ (denote cache_434), placeRow ⟨12, 6, 1, 3⟩ (denote cache_12)] = denote cache_534
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_534

theorem verified_row_535 : fork [place ⟨444, 0, 4, 5⟩ cache_444, place ⟨426, 0, 4, 5⟩ cache_426, place ⟨25, 0, 5, 4⟩ cache_25, place ⟨321, 4, 4, 2⟩ cache_321] = cache_535 := by
  decide +kernel

theorem load_entry_535 : entryAt 535 = entry_535 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_535 : CacheEquation 535 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(535 < 6)), load_entry_535]
  change forkRow [placeRow ⟨444, 0, 4, 5⟩ (denote cache_444), placeRow ⟨426, 0, 4, 5⟩ (denote cache_426), placeRow ⟨25, 0, 5, 4⟩ (denote cache_25), placeRow ⟨321, 4, 4, 2⟩ (denote cache_321)] = denote cache_535
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_535

theorem verified_row_536 : fork [place ⟨307, 0, 4, 3⟩ cache_307, place ⟨244, 0, 5, 4⟩ cache_244, place ⟨26, 3, 4, 3⟩ cache_26, place ⟨534, 0, 5, 2⟩ cache_534] = cache_536 := by
  decide +kernel

theorem load_entry_536 : entryAt 536 = entry_536 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_536 : CacheEquation 536 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(536 < 6)), load_entry_536]
  change forkRow [placeRow ⟨307, 0, 4, 3⟩ (denote cache_307), placeRow ⟨244, 0, 5, 4⟩ (denote cache_244), placeRow ⟨26, 3, 4, 3⟩ (denote cache_26), placeRow ⟨534, 0, 5, 2⟩ (denote cache_534)] = denote cache_536
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_536

theorem verified_row_537 : fork [place ⟨373, 2, 2, 4⟩ cache_373, place ⟨271, 3, 3, 3⟩ cache_271, place ⟨176, 1, 4, 6⟩ cache_176, place ⟨330, 1, 4, 6⟩ cache_330] = cache_537 := by
  decide +kernel

theorem load_entry_537 : entryAt 537 = entry_537 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_537 : CacheEquation 537 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(537 < 6)), load_entry_537]
  change forkRow [placeRow ⟨373, 2, 2, 4⟩ (denote cache_373), placeRow ⟨271, 3, 3, 3⟩ (denote cache_271), placeRow ⟨176, 1, 4, 6⟩ (denote cache_176), placeRow ⟨330, 1, 4, 6⟩ (denote cache_330)] = denote cache_537
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_537

theorem verified_row_538 : fork [place ⟨63, 3, 3, 3⟩ cache_63, place ⟨470, 0, 4, 5⟩ cache_470, place ⟨64, 6, 7, 5⟩ cache_64, place ⟨55, 4, 3, 4⟩ cache_55] = cache_538 := by
  decide +kernel

theorem load_entry_538 : entryAt 538 = entry_538 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_538 : CacheEquation 538 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(538 < 6)), load_entry_538]
  change forkRow [placeRow ⟨63, 3, 3, 3⟩ (denote cache_63), placeRow ⟨470, 0, 4, 5⟩ (denote cache_470), placeRow ⟨64, 6, 7, 5⟩ (denote cache_64), placeRow ⟨55, 4, 3, 4⟩ (denote cache_55)] = denote cache_538
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_538

theorem verified_row_539 : fork [place ⟨51, 1, 5, 4⟩ cache_51, place ⟨488, 3, 4, 3⟩ cache_488, place ⟨428, 0, 5, 4⟩ cache_428, place ⟨516, 0, 5, 4⟩ cache_516] = cache_539 := by
  decide +kernel

theorem load_entry_539 : entryAt 539 = entry_539 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_539 : CacheEquation 539 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(539 < 6)), load_entry_539]
  change forkRow [placeRow ⟨51, 1, 5, 4⟩ (denote cache_51), placeRow ⟨488, 3, 4, 3⟩ (denote cache_488), placeRow ⟨428, 0, 5, 4⟩ (denote cache_428), placeRow ⟨516, 0, 5, 4⟩ (denote cache_516)] = denote cache_539
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_539

theorem verified_row_540 : fork [place ⟨334, 0, 4, 3⟩ cache_334, place ⟨51, 1, 5, 4⟩ cache_51, place ⟨88, 3, 4, 3⟩ cache_88, place ⟨536, 0, 5, 4⟩ cache_536] = cache_540 := by
  decide +kernel

theorem load_entry_540 : entryAt 540 = entry_540 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_540 : CacheEquation 540 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(540 < 6)), load_entry_540]
  change forkRow [placeRow ⟨334, 0, 4, 3⟩ (denote cache_334), placeRow ⟨51, 1, 5, 4⟩ (denote cache_51), placeRow ⟨88, 3, 4, 3⟩ (denote cache_88), placeRow ⟨536, 0, 5, 4⟩ (denote cache_536)] = denote cache_540
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_540

theorem verified_row_541 : fork [place ⟨236, 0, 5, 5⟩ cache_236, place ⟨142, 7, 4, 1⟩ cache_142, place ⟨160, 3, 4, 1⟩ cache_160, place ⟨194, 0, 5, 3⟩ cache_194, place ⟨501, 4, 1, 2⟩ cache_501, place ⟨412, 0, 5, 3⟩ cache_412] = cache_541 := by
  decide +kernel

theorem load_entry_541 : entryAt 541 = entry_541 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_541 : CacheEquation 541 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(541 < 6)), load_entry_541]
  change forkRow [placeRow ⟨236, 0, 5, 5⟩ (denote cache_236), placeRow ⟨142, 7, 4, 1⟩ (denote cache_142), placeRow ⟨160, 3, 4, 1⟩ (denote cache_160), placeRow ⟨194, 0, 5, 3⟩ (denote cache_194), placeRow ⟨501, 4, 1, 2⟩ (denote cache_501), placeRow ⟨412, 0, 5, 3⟩ (denote cache_412)] = denote cache_541
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_541

theorem verified_row_542 : fork [place ⟨6, 5, 5, 0⟩ cache_6, place ⟨442, 0, 4, 5⟩ cache_442] = cache_542 := by
  decide +kernel

theorem load_entry_542 : entryAt 542 = entry_542 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_542 : CacheEquation 542 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(542 < 6)), load_entry_542]
  change forkRow [placeRow ⟨6, 5, 5, 0⟩ (denote cache_6), placeRow ⟨442, 0, 4, 5⟩ (denote cache_442)] = denote cache_542
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_542

theorem verified_row_543 : fork [place ⟨493, 3, 2, 6⟩ cache_493, place ⟨107, 2, 5, 4⟩ cache_107, place ⟨318, 5, 5, 4⟩ cache_318] = cache_543 := by
  decide +kernel

theorem load_entry_543 : entryAt 543 = entry_543 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_543 : CacheEquation 543 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(543 < 6)), load_entry_543]
  change forkRow [placeRow ⟨493, 3, 2, 6⟩ (denote cache_493), placeRow ⟨107, 2, 5, 4⟩ (denote cache_107), placeRow ⟨318, 5, 5, 4⟩ (denote cache_318)] = denote cache_543
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_543

theorem verified_row_544 : fork [place ⟨263, 2, 7, 4⟩ cache_263, place ⟨9, 6, 3, 4⟩ cache_9, place ⟨451, 1, 8, 3⟩ cache_451] = cache_544 := by
  decide +kernel

theorem load_entry_544 : entryAt 544 = entry_544 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_544 : CacheEquation 544 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(544 < 6)), load_entry_544]
  change forkRow [placeRow ⟨263, 2, 7, 4⟩ (denote cache_263), placeRow ⟨9, 6, 3, 4⟩ (denote cache_9), placeRow ⟨451, 1, 8, 3⟩ (denote cache_451)] = denote cache_544
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_544

theorem verified_row_545 : fork [place ⟨256, 0, 4, 5⟩ cache_256, place ⟨448, 0, 5, 4⟩ cache_448, place ⟨153, 0, 6, 3⟩ cache_153, place ⟨343, 0, 4, 5⟩ cache_343] = cache_545 := by
  decide +kernel

theorem load_entry_545 : entryAt 545 = entry_545 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_545 : CacheEquation 545 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(545 < 6)), load_entry_545]
  change forkRow [placeRow ⟨256, 0, 4, 5⟩ (denote cache_256), placeRow ⟨448, 0, 5, 4⟩ (denote cache_448), placeRow ⟨153, 0, 6, 3⟩ (denote cache_153), placeRow ⟨343, 0, 4, 5⟩ (denote cache_343)] = denote cache_545
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_545

theorem verified_row_546 : fork [place ⟨64, 0, 4, 3⟩ cache_64, place ⟨482, 7, 4, 3⟩ cache_482, place ⟨443, 0, 7, 5⟩ cache_443, place ⟨64, 6, 7, 5⟩ cache_64] = cache_546 := by
  decide +kernel

theorem load_entry_546 : entryAt 546 = entry_546 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_546 : CacheEquation 546 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(546 < 6)), load_entry_546]
  change forkRow [placeRow ⟨64, 0, 4, 3⟩ (denote cache_64), placeRow ⟨482, 7, 4, 3⟩ (denote cache_482), placeRow ⟨443, 0, 7, 5⟩ (denote cache_443), placeRow ⟨64, 6, 7, 5⟩ (denote cache_64)] = denote cache_546
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_546

theorem verified_row_547 : fork [place ⟨443, 0, 7, 5⟩ cache_443, place ⟨510, 4, 7, 5⟩ cache_510, place ⟨131, 3, 3, 4⟩ cache_131] = cache_547 := by
  decide +kernel

theorem load_entry_547 : entryAt 547 = entry_547 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_547 : CacheEquation 547 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(547 < 6)), load_entry_547]
  change forkRow [placeRow ⟨443, 0, 7, 5⟩ (denote cache_443), placeRow ⟨510, 4, 7, 5⟩ (denote cache_510), placeRow ⟨131, 3, 3, 4⟩ (denote cache_131)] = denote cache_547
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_547

theorem verified_row_548 : fork [place ⟨426, 0, 4, 5⟩ cache_426, place ⟨541, 0, 4, 5⟩ cache_541, place ⟨25, 0, 5, 4⟩ cache_25, place ⟨321, 4, 4, 2⟩ cache_321] = cache_548 := by
  decide +kernel

theorem load_entry_548 : entryAt 548 = entry_548 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_548 : CacheEquation 548 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(548 < 6)), load_entry_548]
  change forkRow [placeRow ⟨426, 0, 4, 5⟩ (denote cache_426), placeRow ⟨541, 0, 4, 5⟩ (denote cache_541), placeRow ⟨25, 0, 5, 4⟩ (denote cache_25), placeRow ⟨321, 4, 4, 2⟩ (denote cache_321)] = denote cache_548
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_548

theorem verified_row_549 : fork [place ⟨385, 0, 6, 4⟩ cache_385, place ⟨385, 4, 2, 4⟩ cache_385, place ⟨330, 0, 6, 4⟩ cache_330, place ⟨252, 6, 2, 4⟩ cache_252, place ⟨326, 0, 6, 4⟩ cache_326, place ⟨529, 0, 2, 4⟩ cache_529] = cache_549 := by
  decide +kernel

theorem load_entry_549 : entryAt 549 = entry_549 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_549 : CacheEquation 549 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(549 < 6)), load_entry_549]
  change forkRow [placeRow ⟨385, 0, 6, 4⟩ (denote cache_385), placeRow ⟨385, 4, 2, 4⟩ (denote cache_385), placeRow ⟨330, 0, 6, 4⟩ (denote cache_330), placeRow ⟨252, 6, 2, 4⟩ (denote cache_252), placeRow ⟨326, 0, 6, 4⟩ (denote cache_326), placeRow ⟨529, 0, 2, 4⟩ (denote cache_529)] = denote cache_549
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_549

theorem verified_row_550 : fork [place ⟨424, 0, 4, 6⟩ cache_424, place ⟨172, 7, 4, 2⟩ cache_172, place ⟨215, 1, 5, 5⟩ cache_215, place ⟨456, 7, 4, 2⟩ cache_456] = cache_550 := by
  decide +kernel

theorem load_entry_550 : entryAt 550 = entry_550 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_550 : CacheEquation 550 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(550 < 6)), load_entry_550]
  change forkRow [placeRow ⟨424, 0, 4, 6⟩ (denote cache_424), placeRow ⟨172, 7, 4, 2⟩ (denote cache_172), placeRow ⟨215, 1, 5, 5⟩ (denote cache_215), placeRow ⟨456, 7, 4, 2⟩ (denote cache_456)] = denote cache_550
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_550

theorem verified_row_551 : fork [place ⟨300, 6, 4, 3⟩ cache_300, place ⟨172, 7, 4, 3⟩ cache_172, place ⟨319, 3, 5, 7⟩ cache_319, place ⟨527, 4, 5, 7⟩ cache_527, place ⟨176, 5, 4, 3⟩ cache_176] = cache_551 := by
  decide +kernel

theorem load_entry_551 : entryAt 551 = entry_551 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_551 : CacheEquation 551 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(551 < 6)), load_entry_551]
  change forkRow [placeRow ⟨300, 6, 4, 3⟩ (denote cache_300), placeRow ⟨172, 7, 4, 3⟩ (denote cache_172), placeRow ⟨319, 3, 5, 7⟩ (denote cache_319), placeRow ⟨527, 4, 5, 7⟩ (denote cache_527), placeRow ⟨176, 5, 4, 3⟩ (denote cache_176)] = denote cache_551
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_551

theorem verified_row_552 : fork [place ⟨443, 4, 1, 5⟩ cache_443, place ⟨64, 2, 1, 5⟩ cache_64, place ⟨504, 1, 3, 3⟩ cache_504, place ⟨404, 5, 2, 3⟩ cache_404] = cache_552 := by
  decide +kernel

theorem load_entry_552 : entryAt 552 = entry_552 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_552 : CacheEquation 552 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(552 < 6)), load_entry_552]
  change forkRow [placeRow ⟨443, 4, 1, 5⟩ (denote cache_443), placeRow ⟨64, 2, 1, 5⟩ (denote cache_64), placeRow ⟨504, 1, 3, 3⟩ (denote cache_504), placeRow ⟨404, 5, 2, 3⟩ (denote cache_404)] = denote cache_552
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_552

theorem verified_row_553 : fork [place ⟨63, 0, 3, 5⟩ cache_63, place ⟨261, 4, 5, 4⟩ cache_261, place ⟨471, 0, 5, 1⟩ cache_471, place ⟨442, 0, 4, 5⟩ cache_442, place ⟨504, 0, 3, 3⟩ cache_504, place ⟨180, 0, 4, 5⟩ cache_180] = cache_553 := by
  decide +kernel

theorem load_entry_553 : entryAt 553 = entry_553 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_553 : CacheEquation 553 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(553 < 6)), load_entry_553]
  change forkRow [placeRow ⟨63, 0, 3, 5⟩ (denote cache_63), placeRow ⟨261, 4, 5, 4⟩ (denote cache_261), placeRow ⟨471, 0, 5, 1⟩ (denote cache_471), placeRow ⟨442, 0, 4, 5⟩ (denote cache_442), placeRow ⟨504, 0, 3, 3⟩ (denote cache_504), placeRow ⟨180, 0, 4, 5⟩ (denote cache_180)] = denote cache_553
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_553

theorem verified_row_554 : fork [place ⟨30, 6, 5, 4⟩ cache_30, place ⟨96, 7, 4, 5⟩ cache_96, place ⟨474, 0, 4, 5⟩ cache_474] = cache_554 := by
  decide +kernel

theorem load_entry_554 : entryAt 554 = entry_554 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_554 : CacheEquation 554 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(554 < 6)), load_entry_554]
  change forkRow [placeRow ⟨30, 6, 5, 4⟩ (denote cache_30), placeRow ⟨96, 7, 4, 5⟩ (denote cache_96), placeRow ⟨474, 0, 4, 5⟩ (denote cache_474)] = denote cache_554
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_554

theorem verified_row_555 : fork [place ⟨504, 5, 3, 5⟩ cache_504, place ⟨513, 0, 1, 5⟩ cache_513, place ⟨55, 0, 5, 4⟩ cache_55, place ⟨443, 4, 1, 5⟩ cache_443, place ⟨471, 1, 1, 5⟩ cache_471] = cache_555 := by
  decide +kernel

theorem load_entry_555 : entryAt 555 = entry_555 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_555 : CacheEquation 555 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(555 < 6)), load_entry_555]
  change forkRow [placeRow ⟨504, 5, 3, 5⟩ (denote cache_504), placeRow ⟨513, 0, 1, 5⟩ (denote cache_513), placeRow ⟨55, 0, 5, 4⟩ (denote cache_55), placeRow ⟨443, 4, 1, 5⟩ (denote cache_443), placeRow ⟨471, 1, 1, 5⟩ (denote cache_471)] = denote cache_555
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_555

theorem verified_row_556 : fork [place ⟨34, 1, 4, 2⟩ cache_34, place ⟨549, 0, 3, 4⟩ cache_549] = cache_556 := by
  decide +kernel

theorem load_entry_556 : entryAt 556 = entry_556 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_556 : CacheEquation 556 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(556 < 6)), load_entry_556]
  change forkRow [placeRow ⟨34, 1, 4, 2⟩ (denote cache_34), placeRow ⟨549, 0, 3, 4⟩ (denote cache_549)] = denote cache_556
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_556

theorem verified_row_557 : fork [place ⟨460, 0, 5, 4⟩ cache_460, place ⟨460, 4, 2, 4⟩ cache_460, place ⟨460, 2, 5, 4⟩ cache_460, place ⟨411, 4, 5, 4⟩ cache_411, place ⟨531, 0, 3, 6⟩ cache_531, place ⟨531, 4, 4, 6⟩ cache_531, place ⟨406, 5, 5, 4⟩ cache_406] = cache_557 := by
  decide +kernel

theorem load_entry_557 : entryAt 557 = entry_557 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_557 : CacheEquation 557 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(557 < 6)), load_entry_557]
  change forkRow [placeRow ⟨460, 0, 5, 4⟩ (denote cache_460), placeRow ⟨460, 4, 2, 4⟩ (denote cache_460), placeRow ⟨460, 2, 5, 4⟩ (denote cache_460), placeRow ⟨411, 4, 5, 4⟩ (denote cache_411), placeRow ⟨531, 0, 3, 6⟩ (denote cache_531), placeRow ⟨531, 4, 4, 6⟩ (denote cache_531), placeRow ⟨406, 5, 5, 4⟩ (denote cache_406)] = denote cache_557
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_557

theorem verified_row_558 : fork [place ⟨180, 5, 5, 4⟩ cache_180, place ⟨443, 4, 1, 5⟩ cache_443, place ⟨513, 0, 1, 5⟩ cache_513, place ⟨442, 1, 5, 4⟩ cache_442] = cache_558 := by
  decide +kernel

theorem load_entry_558 : entryAt 558 = entry_558 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_558 : CacheEquation 558 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(558 < 6)), load_entry_558]
  change forkRow [placeRow ⟨180, 5, 5, 4⟩ (denote cache_180), placeRow ⟨443, 4, 1, 5⟩ (denote cache_443), placeRow ⟨513, 0, 1, 5⟩ (denote cache_513), placeRow ⟨442, 1, 5, 4⟩ (denote cache_442)] = denote cache_558
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_558

theorem verified_row_559 : fork [place ⟨228, 4, 5, 2⟩ cache_228, place ⟨7, 3, 3, 4⟩ cache_7, place ⟨155, 4, 4, 5⟩ cache_155, place ⟨538, 5, 4, 5⟩ cache_538] = cache_559 := by
  decide +kernel

theorem load_entry_559 : entryAt 559 = entry_559 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_559 : CacheEquation 559 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(559 < 6)), load_entry_559]
  change forkRow [placeRow ⟨228, 4, 5, 2⟩ (denote cache_228), placeRow ⟨7, 3, 3, 4⟩ (denote cache_7), placeRow ⟨155, 4, 4, 5⟩ (denote cache_155), placeRow ⟨538, 5, 4, 5⟩ (denote cache_538)] = denote cache_559
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_559

end SnakyCertificate.Check

end OAI
