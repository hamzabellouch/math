import OAI.Combinatorics.SnakyCertificate.Cache
import OAI.Combinatorics.SnakyCertificate.TableList

namespace OAI

namespace SnakyCertificate.Check

theorem verified_row_440 : fork [place ⟨6, 6, 1, 3⟩ cache_6, place ⟨435, 0, 2, 5⟩ cache_435] = cache_440 := by
  decide +kernel

theorem load_entry_440 : entryAt 440 = entry_440 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_440 : CacheEquation 440 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(440 < 6)), load_entry_440]
  change forkRow [placeRow ⟨6, 6, 1, 3⟩ (denote cache_6), placeRow ⟨435, 0, 2, 5⟩ (denote cache_435)] = denote cache_440
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_440

theorem verified_row_441 : fork [place ⟨6, 6, 3, 4⟩ cache_6, place ⟨435, 0, 4, 6⟩ cache_435] = cache_441 := by
  decide +kernel

theorem load_entry_441 : entryAt 441 = entry_441 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_441 : CacheEquation 441 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(441 < 6)), load_entry_441]
  change forkRow [placeRow ⟨6, 6, 3, 4⟩ (denote cache_6), placeRow ⟨435, 0, 4, 6⟩ (denote cache_435)] = denote cache_441
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_441

theorem verified_row_442 : fork [place ⟨63, 0, 3, 5⟩ cache_63, place ⟨7, 1, 5, 4⟩ cache_7, place ⟨433, 0, 4, 5⟩ cache_433, place ⟨201, 0, 3, 2⟩ cache_201] = cache_442 := by
  decide +kernel

theorem load_entry_442 : entryAt 442 = entry_442 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_442 : CacheEquation 442 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(442 < 6)), load_entry_442]
  change forkRow [placeRow ⟨63, 0, 3, 5⟩ (denote cache_63), placeRow ⟨7, 1, 5, 4⟩ (denote cache_7), placeRow ⟨433, 0, 4, 5⟩ (denote cache_433), placeRow ⟨201, 0, 3, 2⟩ (denote cache_201)] = denote cache_442
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_442

theorem verified_row_443 : fork [place ⟨6, 0, 5, 4⟩ cache_6, place ⟨438, 0, 3, 4⟩ cache_438] = cache_443 := by
  decide +kernel

theorem load_entry_443 : entryAt 443 = entry_443 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_443 : CacheEquation 443 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(443 < 6)), load_entry_443]
  change forkRow [placeRow ⟨6, 0, 5, 4⟩ (denote cache_6), placeRow ⟨438, 0, 3, 4⟩ (denote cache_438)] = denote cache_443
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_443

theorem verified_row_444 : fork [place ⟨194, 0, 5, 3⟩ cache_194, place ⟨160, 3, 4, 1⟩ cache_160, place ⟨142, 7, 4, 1⟩ cache_142, place ⟨236, 0, 5, 5⟩ cache_236, place ⟨353, 4, 1, 2⟩ cache_353, place ⟨412, 0, 5, 3⟩ cache_412] = cache_444 := by
  decide +kernel

theorem load_entry_444 : entryAt 444 = entry_444 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_444 : CacheEquation 444 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(444 < 6)), load_entry_444]
  change forkRow [placeRow ⟨194, 0, 5, 3⟩ (denote cache_194), placeRow ⟨160, 3, 4, 1⟩ (denote cache_160), placeRow ⟨142, 7, 4, 1⟩ (denote cache_142), placeRow ⟨236, 0, 5, 5⟩ (denote cache_236), placeRow ⟨353, 4, 1, 2⟩ (denote cache_353), placeRow ⟨412, 0, 5, 3⟩ (denote cache_412)] = denote cache_444
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_444

theorem verified_row_445 : fork [place ⟨9, 4, 3, 4⟩ cache_9, place ⟨432, 0, 5, 7⟩ cache_432] = cache_445 := by
  decide +kernel

theorem load_entry_445 : entryAt 445 = entry_445 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_445 : CacheEquation 445 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(445 < 6)), load_entry_445]
  change forkRow [placeRow ⟨9, 4, 3, 4⟩ (denote cache_9), placeRow ⟨432, 0, 5, 7⟩ (denote cache_432)] = denote cache_445
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_445

theorem verified_row_446 : fork [place ⟨4, 6, 4, 3⟩ cache_4, place ⟨438, 0, 6, 5⟩ cache_438] = cache_446 := by
  decide +kernel

theorem load_entry_446 : entryAt 446 = entry_446 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_446 : CacheEquation 446 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(446 < 6)), load_entry_446]
  change forkRow [placeRow ⟨4, 6, 4, 3⟩ (denote cache_4), placeRow ⟨438, 0, 6, 5⟩ (denote cache_438)] = denote cache_446
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_446

theorem verified_row_447 : fork [place ⟨0, 0, 0, 3⟩ cache_0, place ⟨436, 4, 4, 6⟩ cache_436] = cache_447 := by
  decide +kernel

theorem load_entry_447 : entryAt 447 = entry_447 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_447 : CacheEquation 447 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(447 < 6)), load_entry_447]
  change forkRow [placeRow ⟨0, 0, 0, 3⟩ (denote cache_0), placeRow ⟨436, 4, 4, 6⟩ (denote cache_436)] = denote cache_447
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_447

theorem verified_row_448 : fork [place ⟨9, 4, 1, 3⟩ cache_9, place ⟨436, 0, 3, 6⟩ cache_436] = cache_448 := by
  decide +kernel

theorem load_entry_448 : entryAt 448 = entry_448 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_448 : CacheEquation 448 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(448 < 6)), load_entry_448]
  change forkRow [placeRow ⟨9, 4, 1, 3⟩ (denote cache_9), placeRow ⟨436, 0, 3, 6⟩ (denote cache_436)] = denote cache_448
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_448

theorem verified_row_449 : fork [place ⟨26, 3, 4, 3⟩ cache_26, place ⟨244, 0, 5, 4⟩ cache_244, place ⟨439, 0, 5, 4⟩ cache_439, place ⟨307, 0, 4, 3⟩ cache_307] = cache_449 := by
  decide +kernel

theorem load_entry_449 : entryAt 449 = entry_449 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_449 : CacheEquation 449 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(449 < 6)), load_entry_449]
  change forkRow [placeRow ⟨26, 3, 4, 3⟩ (denote cache_26), placeRow ⟨244, 0, 5, 4⟩ (denote cache_244), placeRow ⟨439, 0, 5, 4⟩ (denote cache_439), placeRow ⟨307, 0, 4, 3⟩ (denote cache_307)] = denote cache_449
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_449

theorem verified_row_450 : fork [place ⟨6, 1, 5, 5⟩ cache_6, place ⟨440, 0, 6, 4⟩ cache_440] = cache_450 := by
  decide +kernel

theorem load_entry_450 : entryAt 450 = entry_450 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_450 : CacheEquation 450 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(450 < 6)), load_entry_450]
  change forkRow [placeRow ⟨6, 1, 5, 5⟩ (denote cache_6), placeRow ⟨440, 0, 6, 4⟩ (denote cache_440)] = denote cache_450
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_450

theorem verified_row_451 : fork [place ⟨1, 5, 4, 3⟩ cache_1, place ⟨449, 0, 5, 4⟩ cache_449] = cache_451 := by
  decide +kernel

theorem load_entry_451 : entryAt 451 = entry_451 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_451 : CacheEquation 451 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(451 < 6)), load_entry_451]
  change forkRow [placeRow ⟨1, 5, 4, 3⟩ (denote cache_1), placeRow ⟨449, 0, 5, 4⟩ (denote cache_449)] = denote cache_451
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_451

theorem verified_row_452 : fork [place ⟨24, 1, 5, 7⟩ cache_24, place ⟨451, 0, 3, 8⟩ cache_451, place ⟨25, 3, 3, 7⟩ cache_25] = cache_452 := by
  decide +kernel

theorem load_entry_452 : entryAt 452 = entry_452 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_452 : CacheEquation 452 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(452 < 6)), load_entry_452]
  change forkRow [placeRow ⟨24, 1, 5, 7⟩ (denote cache_24), placeRow ⟨451, 0, 3, 8⟩ (denote cache_451), placeRow ⟨25, 3, 3, 7⟩ (denote cache_25)] = denote cache_452
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_452

theorem verified_row_453 : fork [place ⟨359, 0, 4, 3⟩ cache_359, place ⟨226, 7, 3, 1⟩ cache_226, place ⟨386, 4, 2, 4⟩ cache_386, place ⟨389, 1, 5, 4⟩ cache_389, place ⟨414, 4, 3, 3⟩ cache_414] = cache_453 := by
  decide +kernel

theorem load_entry_453 : entryAt 453 = entry_453 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_453 : CacheEquation 453 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(453 < 6)), load_entry_453]
  change forkRow [placeRow ⟨359, 0, 4, 3⟩ (denote cache_359), placeRow ⟨226, 7, 3, 1⟩ (denote cache_226), placeRow ⟨386, 4, 2, 4⟩ (denote cache_386), placeRow ⟨389, 1, 5, 4⟩ (denote cache_389), placeRow ⟨414, 4, 3, 3⟩ (denote cache_414)] = denote cache_453
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_453

theorem verified_row_454 : fork [place ⟨58, 0, 6, 3⟩ cache_58, place ⟨436, 0, 3, 6⟩ cache_436] = cache_454 := by
  decide +kernel

theorem load_entry_454 : entryAt 454 = entry_454 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_454 : CacheEquation 454 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(454 < 6)), load_entry_454]
  change forkRow [placeRow ⟨58, 0, 6, 3⟩ (denote cache_58), placeRow ⟨436, 0, 3, 6⟩ (denote cache_436)] = denote cache_454
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_454

theorem verified_row_455 : fork [place ⟨20, 2, 4, 5⟩ cache_20, place ⟨118, 3, 0, 5⟩ cache_118, place ⟨39, 2, 3, 4⟩ cache_39] = cache_455 := by
  decide +kernel

theorem load_entry_455 : entryAt 455 = entry_455 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_455 : CacheEquation 455 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(455 < 6)), load_entry_455]
  change forkRow [placeRow ⟨20, 2, 4, 5⟩ (denote cache_20), placeRow ⟨118, 3, 0, 5⟩ (denote cache_118), placeRow ⟨39, 2, 3, 4⟩ (denote cache_39)] = denote cache_455
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_455

theorem verified_row_456 : fork [place ⟨308, 4, 4, 3⟩ cache_308, place ⟨64, 2, 1, 5⟩ cache_64, place ⟨63, 1, 5, 3⟩ cache_63, place ⟨55, 0, 5, 4⟩ cache_55] = cache_456 := by
  decide +kernel

theorem load_entry_456 : entryAt 456 = entry_456 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_456 : CacheEquation 456 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(456 < 6)), load_entry_456]
  change forkRow [placeRow ⟨308, 4, 4, 3⟩ (denote cache_308), placeRow ⟨64, 2, 1, 5⟩ (denote cache_64), placeRow ⟨63, 1, 5, 3⟩ (denote cache_63), placeRow ⟨55, 0, 5, 4⟩ (denote cache_55)] = denote cache_456
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_456

theorem verified_row_457 : fork [place ⟨28, 7, 3, 2⟩ cache_28, place ⟨454, 0, 5, 4⟩ cache_454] = cache_457 := by
  decide +kernel

theorem load_entry_457 : entryAt 457 = entry_457 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_457 : CacheEquation 457 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(457 < 6)), load_entry_457]
  change forkRow [placeRow ⟨28, 7, 3, 2⟩ (denote cache_28), placeRow ⟨454, 0, 5, 4⟩ (denote cache_454)] = denote cache_457
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_457

theorem verified_row_458 : fork [place ⟨130, 1, 4, 2⟩ cache_130, place ⟨177, 1, 4, 2⟩ cache_177, place ⟨450, 0, 1, 4⟩ cache_450] = cache_458 := by
  decide +kernel

theorem load_entry_458 : entryAt 458 = entry_458 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_458 : CacheEquation 458 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(458 < 6)), load_entry_458]
  change forkRow [placeRow ⟨130, 1, 4, 2⟩ (denote cache_130), placeRow ⟨177, 1, 4, 2⟩ (denote cache_177), placeRow ⟨450, 0, 1, 4⟩ (denote cache_450)] = denote cache_458
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_458

theorem verified_row_459 : fork [place ⟨97, 2, 7, 3⟩ cache_97, place ⟨448, 0, 5, 4⟩ cache_448, place ⟨65, 2, 7, 3⟩ cache_65] = cache_459 := by
  decide +kernel

theorem load_entry_459 : entryAt 459 = entry_459 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_459 : CacheEquation 459 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(459 < 6)), load_entry_459]
  change forkRow [placeRow ⟨97, 2, 7, 3⟩ (denote cache_97), placeRow ⟨448, 0, 5, 4⟩ (denote cache_448), placeRow ⟨65, 2, 7, 3⟩ (denote cache_65)] = denote cache_459
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_459

theorem verified_row_460 : fork [place ⟨183, 6, 1, 4⟩ cache_183, place ⟨173, 2, 5, 4⟩ cache_173, place ⟨295, 0, 5, 4⟩ cache_295, place ⟨282, 4, 1, 4⟩ cache_282, place ⟨246, 2, 5, 4⟩ cache_246, place ⟨263, 2, 5, 4⟩ cache_263, place ⟨220, 2, 5, 4⟩ cache_220] = cache_460 := by
  decide +kernel

theorem load_entry_460 : entryAt 460 = entry_460 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_460 : CacheEquation 460 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(460 < 6)), load_entry_460]
  change forkRow [placeRow ⟨183, 6, 1, 4⟩ (denote cache_183), placeRow ⟨173, 2, 5, 4⟩ (denote cache_173), placeRow ⟨295, 0, 5, 4⟩ (denote cache_295), placeRow ⟨282, 4, 1, 4⟩ (denote cache_282), placeRow ⟨246, 2, 5, 4⟩ (denote cache_246), placeRow ⟨263, 2, 5, 4⟩ (denote cache_263), placeRow ⟨220, 2, 5, 4⟩ (denote cache_220)] = denote cache_460
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_460

theorem verified_row_461 : fork [place ⟨4, 1, 4, 3⟩ cache_4, place ⟨458, 0, 6, 4⟩ cache_458] = cache_461 := by
  decide +kernel

theorem load_entry_461 : entryAt 461 = entry_461 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_461 : CacheEquation 461 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(461 < 6)), load_entry_461]
  change forkRow [placeRow ⟨4, 1, 4, 3⟩ (denote cache_4), placeRow ⟨458, 0, 6, 4⟩ (denote cache_458)] = denote cache_461
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_461

theorem verified_row_462 : fork [place ⟨452, 0, 3, 2⟩ cache_452, place ⟨86, 0, 5, 4⟩ cache_86, place ⟨328, 1, 5, 4⟩ cache_328] = cache_462 := by
  decide +kernel

theorem load_entry_462 : entryAt 462 = entry_462 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_462 : CacheEquation 462 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(462 < 6)), load_entry_462]
  change forkRow [placeRow ⟨452, 0, 3, 2⟩ (denote cache_452), placeRow ⟨86, 0, 5, 4⟩ (denote cache_86), placeRow ⟨328, 1, 5, 4⟩ (denote cache_328)] = denote cache_462
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_462

theorem verified_row_463 : fork [place ⟨170, 0, 6, 3⟩ cache_170, place ⟨76, 1, 3, 2⟩ cache_76, place ⟨447, 0, 5, 4⟩ cache_447] = cache_463 := by
  decide +kernel

theorem load_entry_463 : entryAt 463 = entry_463 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_463 : CacheEquation 463 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(463 < 6)), load_entry_463]
  change forkRow [placeRow ⟨170, 0, 6, 3⟩ (denote cache_170), placeRow ⟨76, 1, 3, 2⟩ (denote cache_76), placeRow ⟨447, 0, 5, 4⟩ (denote cache_447)] = denote cache_463
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_463

theorem verified_row_464 : fork [place ⟨63, 0, 3, 5⟩ cache_63, place ⟨224, 0, 5, 4⟩ cache_224, place ⟨315, 0, 7, 3⟩ cache_315, place ⟨306, 0, 5, 5⟩ cache_306, place ⟨358, 0, 7, 3⟩ cache_358, place ⟨461, 0, 5, 5⟩ cache_461] = cache_464 := by
  decide +kernel

theorem load_entry_464 : entryAt 464 = entry_464 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_464 : CacheEquation 464 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(464 < 6)), load_entry_464]
  change forkRow [placeRow ⟨63, 0, 3, 5⟩ (denote cache_63), placeRow ⟨224, 0, 5, 4⟩ (denote cache_224), placeRow ⟨315, 0, 7, 3⟩ (denote cache_315), placeRow ⟨306, 0, 5, 5⟩ (denote cache_306), placeRow ⟨358, 0, 7, 3⟩ (denote cache_358), placeRow ⟨461, 0, 5, 5⟩ (denote cache_461)] = denote cache_464
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_464

theorem verified_row_465 : fork [place ⟨55, 3, 4, 5⟩ cache_55, place ⟨285, 0, 3, 4⟩ cache_285, place ⟨64, 1, 3, 1⟩ cache_64] = cache_465 := by
  decide +kernel

theorem load_entry_465 : entryAt 465 = entry_465 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_465 : CacheEquation 465 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(465 < 6)), load_entry_465]
  change forkRow [placeRow ⟨55, 3, 4, 5⟩ (denote cache_55), placeRow ⟨285, 0, 3, 4⟩ (denote cache_285), placeRow ⟨64, 1, 3, 1⟩ (denote cache_64)] = denote cache_465
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_465

theorem verified_row_466 : fork [place ⟨395, 4, 3, 4⟩ cache_395, place ⟨360, 4, 2, 6⟩ cache_360, place ⟨417, 1, 5, 4⟩ cache_417, place ⟨325, 4, 3, 4⟩ cache_325, place ⟨324, 4, 3, 5⟩ cache_324] = cache_466 := by
  decide +kernel

theorem load_entry_466 : entryAt 466 = entry_466 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_466 : CacheEquation 466 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(466 < 6)), load_entry_466]
  change forkRow [placeRow ⟨395, 4, 3, 4⟩ (denote cache_395), placeRow ⟨360, 4, 2, 6⟩ (denote cache_360), placeRow ⟨417, 1, 5, 4⟩ (denote cache_417), placeRow ⟨325, 4, 3, 4⟩ (denote cache_325), placeRow ⟨324, 4, 3, 5⟩ (denote cache_324)] = denote cache_466
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_466

theorem verified_row_467 : fork [place ⟨64, 7, 5, 7⟩ cache_64, place ⟨314, 6, 5, 4⟩ cache_314, place ⟨443, 1, 5, 7⟩ cache_443] = cache_467 := by
  decide +kernel

theorem load_entry_467 : entryAt 467 = entry_467 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_467 : CacheEquation 467 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(467 < 6)), load_entry_467]
  change forkRow [placeRow ⟨64, 7, 5, 7⟩ (denote cache_64), placeRow ⟨314, 6, 5, 4⟩ (denote cache_314), placeRow ⟨443, 1, 5, 7⟩ (denote cache_443)] = denote cache_467
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_467

theorem verified_row_468 : fork [place ⟨6, 6, 3, 4⟩ cache_6, place ⟨464, 0, 4, 7⟩ cache_464] = cache_468 := by
  decide +kernel

theorem load_entry_468 : entryAt 468 = entry_468 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_468 : CacheEquation 468 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(468 < 6)), load_entry_468]
  change forkRow [placeRow ⟨6, 6, 3, 4⟩ (denote cache_6), placeRow ⟨464, 0, 4, 7⟩ (denote cache_464)] = denote cache_468
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_468

theorem verified_row_469 : fork [place ⟨55, 5, 4, 3⟩ cache_55, place ⟨443, 1, 5, 7⟩ cache_443, place ⟨314, 6, 5, 4⟩ cache_314] = cache_469 := by
  decide +kernel

theorem load_entry_469 : entryAt 469 = entry_469 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_469 : CacheEquation 469 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(469 < 6)), load_entry_469]
  change forkRow [placeRow ⟨55, 5, 4, 3⟩ (denote cache_55), placeRow ⟨443, 1, 5, 7⟩ (denote cache_443), placeRow ⟨314, 6, 5, 4⟩ (denote cache_314)] = denote cache_469
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_469

theorem verified_row_470 : fork [place ⟨6, 4, 3, 4⟩ cache_6, place ⟨468, 0, 4, 2⟩ cache_468] = cache_470 := by
  decide +kernel

theorem load_entry_470 : entryAt 470 = entry_470 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_470 : CacheEquation 470 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(470 < 6)), load_entry_470]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (denote cache_6), placeRow ⟨468, 0, 4, 2⟩ (denote cache_468)] = denote cache_470
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_470

theorem verified_row_471 : fork [place ⟨6, 5, 4, 3⟩ cache_6, place ⟨466, 0, 5, 6⟩ cache_466] = cache_471 := by
  decide +kernel

theorem load_entry_471 : entryAt 471 = entry_471 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_471 : CacheEquation 471 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(471 < 6)), load_entry_471]
  change forkRow [placeRow ⟨6, 5, 4, 3⟩ (denote cache_6), placeRow ⟨466, 0, 5, 6⟩ (denote cache_466)] = denote cache_471
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_471

theorem verified_row_472 : fork [place ⟨6, 5, 5, 0⟩ cache_6, place ⟨466, 0, 6, 3⟩ cache_466] = cache_472 := by
  decide +kernel

theorem load_entry_472 : entryAt 472 = entry_472 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_472 : CacheEquation 472 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(472 < 6)), load_entry_472]
  change forkRow [placeRow ⟨6, 5, 5, 0⟩ (denote cache_6), placeRow ⟨466, 0, 6, 3⟩ (denote cache_466)] = denote cache_472
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_472

theorem verified_row_473 : fork [place ⟨121, 5, 5, 4⟩ cache_121, place ⟨436, 0, 3, 7⟩ cache_436, place ⟨445, 4, 5, 4⟩ cache_445] = cache_473 := by
  decide +kernel

theorem load_entry_473 : entryAt 473 = entry_473 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_473 : CacheEquation 473 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(473 < 6)), load_entry_473]
  change forkRow [placeRow ⟨121, 5, 5, 4⟩ (denote cache_121), placeRow ⟨436, 0, 3, 7⟩ (denote cache_436), placeRow ⟨445, 4, 5, 4⟩ (denote cache_445)] = denote cache_473
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_473

theorem verified_row_474 : fork [place ⟨463, 0, 6, 5⟩ cache_463, place ⟨70, 0, 3, 5⟩ cache_70, place ⟨83, 1, 5, 3⟩ cache_83] = cache_474 := by
  decide +kernel

theorem load_entry_474 : entryAt 474 = entry_474 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_474 : CacheEquation 474 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(474 < 6)), load_entry_474]
  change forkRow [placeRow ⟨463, 0, 6, 5⟩ (denote cache_463), placeRow ⟨70, 0, 3, 5⟩ (denote cache_70), placeRow ⟨83, 1, 5, 3⟩ (denote cache_83)] = denote cache_474
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_474

theorem verified_row_475 : fork [place ⟨63, 1, 5, 3⟩ cache_63, place ⟨261, 1, 4, 3⟩ cache_261, place ⟨457, 0, 2, 5⟩ cache_457, place ⟨269, 2, 2, 5⟩ cache_269] = cache_475 := by
  decide +kernel

theorem load_entry_475 : entryAt 475 = entry_475 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_475 : CacheEquation 475 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(475 < 6)), load_entry_475]
  change forkRow [placeRow ⟨63, 1, 5, 3⟩ (denote cache_63), placeRow ⟨261, 1, 4, 3⟩ (denote cache_261), placeRow ⟨457, 0, 2, 5⟩ (denote cache_457), placeRow ⟨269, 2, 2, 5⟩ (denote cache_269)] = denote cache_475
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_475

theorem verified_row_476 : fork [place ⟨0, 0, 1, 3⟩ cache_0, place ⟨473, 0, 5, 3⟩ cache_473] = cache_476 := by
  decide +kernel

theorem load_entry_476 : entryAt 476 = entry_476 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_476 : CacheEquation 476 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(476 < 6)), load_entry_476]
  change forkRow [placeRow ⟨0, 0, 1, 3⟩ (denote cache_0), placeRow ⟨473, 0, 5, 3⟩ (denote cache_473)] = denote cache_476
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_476

theorem verified_row_477 : fork [place ⟨55, 1, 4, 5⟩ cache_55, place ⟨154, 7, 4, 5⟩ cache_154, place ⟨154, 3, 4, 0⟩ cache_154, place ⟨471, 2, 5, 4⟩ cache_471] = cache_477 := by
  decide +kernel

theorem load_entry_477 : entryAt 477 = entry_477 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_477 : CacheEquation 477 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(477 < 6)), load_entry_477]
  change forkRow [placeRow ⟨55, 1, 4, 5⟩ (denote cache_55), placeRow ⟨154, 7, 4, 5⟩ (denote cache_154), placeRow ⟨154, 3, 4, 0⟩ (denote cache_154), placeRow ⟨471, 2, 5, 4⟩ (denote cache_471)] = denote cache_477
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_477

theorem verified_row_478 : fork [place ⟨25, 3, 4, 5⟩ cache_25, place ⟨165, 2, 4, 5⟩ cache_165, place ⟨190, 0, 7, 4⟩ cache_190] = cache_478 := by
  decide +kernel

theorem load_entry_478 : entryAt 478 = entry_478 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_478 : CacheEquation 478 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(478 < 6)), load_entry_478]
  change forkRow [placeRow ⟨25, 3, 4, 5⟩ (denote cache_25), placeRow ⟨165, 2, 4, 5⟩ (denote cache_165), placeRow ⟨190, 0, 7, 4⟩ (denote cache_190)] = denote cache_478
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_478

theorem verified_row_479 : fork [place ⟨55, 0, 5, 4⟩ cache_55, place ⟨443, 0, 4, 5⟩ cache_443, place ⟨443, 4, 1, 5⟩ cache_443] = cache_479 := by
  decide +kernel

theorem load_entry_479 : entryAt 479 = entry_479 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_479 : CacheEquation 479 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(479 < 6)), load_entry_479]
  change forkRow [placeRow ⟨55, 0, 5, 4⟩ (denote cache_55), placeRow ⟨443, 0, 4, 5⟩ (denote cache_443), placeRow ⟨443, 4, 1, 5⟩ (denote cache_443)] = denote cache_479
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_479

end SnakyCertificate.Check

end OAI
