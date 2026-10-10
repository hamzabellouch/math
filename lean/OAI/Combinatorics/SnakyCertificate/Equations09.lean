import OAI.Combinatorics.SnakyCertificate.Cache
import OAI.Combinatorics.SnakyCertificate.TableList

namespace OAI

namespace SnakyCertificate.Check

theorem verified_row_360 : fork [place ⟨155, 4, 4, 5⟩ cache_155, place ⟨7, 3, 3, 4⟩ cache_7, place ⟨337, 0, 5, 2⟩ cache_337, place ⟨228, 4, 5, 2⟩ cache_228] = cache_360 := by
  decide +kernel

theorem load_entry_360 : entryAt 360 = entry_360 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_360 : CacheEquation 360 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(360 < 6)), load_entry_360]
  change forkRow [placeRow ⟨155, 4, 4, 5⟩ (denote cache_155), placeRow ⟨7, 3, 3, 4⟩ (denote cache_7), placeRow ⟨337, 0, 5, 2⟩ (denote cache_337), placeRow ⟨228, 4, 5, 2⟩ (denote cache_228)] = denote cache_360
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_360

theorem verified_row_361 : fork [place ⟨6, 4, 3, 4⟩ cache_6, place ⟨352, 0, 4, 5⟩ cache_352] = cache_361 := by
  decide +kernel

theorem load_entry_361 : entryAt 361 = entry_361 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_361 : CacheEquation 361 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(361 < 6)), load_entry_361]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (denote cache_6), placeRow ⟨352, 0, 4, 5⟩ (denote cache_352)] = denote cache_361
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_361

theorem verified_row_362 : fork [place ⟨4, 0, 3, 4⟩ cache_4, place ⟨345, 0, 4, 3⟩ cache_345] = cache_362 := by
  decide +kernel

theorem load_entry_362 : entryAt 362 = entry_362 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_362 : CacheEquation 362 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(362 < 6)), load_entry_362]
  change forkRow [placeRow ⟨4, 0, 3, 4⟩ (denote cache_4), placeRow ⟨345, 0, 4, 3⟩ (denote cache_345)] = denote cache_362
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_362

theorem verified_row_363 : fork [place ⟨137, 1, 4, 2⟩ cache_137, place ⟨248, 0, 2, 4⟩ cache_248] = cache_363 := by
  decide +kernel

theorem load_entry_363 : entryAt 363 = entry_363 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_363 : CacheEquation 363 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(363 < 6)), load_entry_363]
  change forkRow [placeRow ⟨137, 1, 4, 2⟩ (denote cache_137), placeRow ⟨248, 0, 2, 4⟩ (denote cache_248)] = denote cache_363
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_363

theorem verified_row_364 : fork [place ⟨63, 0, 3, 5⟩ cache_63, place ⟨314, 2, 3, 1⟩ cache_314] = cache_364 := by
  decide +kernel

theorem load_entry_364 : entryAt 364 = entry_364 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_364 : CacheEquation 364 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(364 < 6)), load_entry_364]
  change forkRow [placeRow ⟨63, 0, 3, 5⟩ (denote cache_63), placeRow ⟨314, 2, 3, 1⟩ (denote cache_314)] = denote cache_364
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_364

theorem verified_row_365 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨354, 0, 4, 3⟩ cache_354] = cache_365 := by
  decide +kernel

theorem load_entry_365 : entryAt 365 = entry_365 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_365 : CacheEquation 365 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(365 < 6)), load_entry_365]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨354, 0, 4, 3⟩ (denote cache_354)] = denote cache_365
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_365

theorem verified_row_366 : fork [place ⟨6, 3, 4, 5⟩ cache_6, place ⟨357, 0, 6, 2⟩ cache_357] = cache_366 := by
  decide +kernel

theorem load_entry_366 : entryAt 366 = entry_366 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_366 : CacheEquation 366 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(366 < 6)), load_entry_366]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (denote cache_6), placeRow ⟨357, 0, 6, 2⟩ (denote cache_357)] = denote cache_366
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_366

theorem verified_row_367 : fork [place ⟨6, 2, 5, 4⟩ cache_6, place ⟨361, 4, 4, 6⟩ cache_361] = cache_367 := by
  decide +kernel

theorem load_entry_367 : entryAt 367 = entry_367 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_367 : CacheEquation 367 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(367 < 6)), load_entry_367]
  change forkRow [placeRow ⟨6, 2, 5, 4⟩ (denote cache_6), placeRow ⟨361, 4, 4, 6⟩ (denote cache_361)] = denote cache_367
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_367

theorem verified_row_368 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨366, 0, 2, 4⟩ cache_366] = cache_368 := by
  decide +kernel

theorem load_entry_368 : entryAt 368 = entry_368 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_368 : CacheEquation 368 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(368 < 6)), load_entry_368]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨366, 0, 2, 4⟩ (denote cache_366)] = denote cache_368
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_368

theorem verified_row_369 : fork [place ⟨6, 0, 5, 4⟩ cache_6, place ⟨367, 4, 1, 2⟩ cache_367] = cache_369 := by
  decide +kernel

theorem load_entry_369 : entryAt 369 = entry_369 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_369 : CacheEquation 369 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(369 < 6)), load_entry_369]
  change forkRow [placeRow ⟨6, 0, 5, 4⟩ (denote cache_6), placeRow ⟨367, 4, 1, 2⟩ (denote cache_367)] = denote cache_369
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_369

theorem verified_row_370 : fork [place ⟨199, 3, 1, 4⟩ cache_199, place ⟨286, 1, 5, 4⟩ cache_286, place ⟨24, 6, 1, 3⟩ cache_24, place ⟨319, 0, 5, 3⟩ cache_319] = cache_370 := by
  decide +kernel

theorem load_entry_370 : entryAt 370 = entry_370 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_370 : CacheEquation 370 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(370 < 6)), load_entry_370]
  change forkRow [placeRow ⟨199, 3, 1, 4⟩ (denote cache_199), placeRow ⟨286, 1, 5, 4⟩ (denote cache_286), placeRow ⟨24, 6, 1, 3⟩ (denote cache_24), placeRow ⟨319, 0, 5, 3⟩ (denote cache_319)] = denote cache_370
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_370

theorem verified_row_371 : fork [place ⟨267, 6, 2, 4⟩ cache_267, place ⟨137, 1, 4, 2⟩ cache_137] = cache_371 := by
  decide +kernel

theorem load_entry_371 : entryAt 371 = entry_371 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_371 : CacheEquation 371 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(371 < 6)), load_entry_371]
  change forkRow [placeRow ⟨267, 6, 2, 4⟩ (denote cache_267), placeRow ⟨137, 1, 4, 2⟩ (denote cache_137)] = denote cache_371
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_371

theorem verified_row_372 : fork [place ⟨40, 1, 4, 3⟩ cache_40, place ⟨333, 0, 2, 4⟩ cache_333, place ⟨120, 1, 3, 3⟩ cache_120, place ⟨161, 0, 4, 2⟩ cache_161] = cache_372 := by
  decide +kernel

theorem load_entry_372 : entryAt 372 = entry_372 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_372 : CacheEquation 372 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(372 < 6)), load_entry_372]
  change forkRow [placeRow ⟨40, 1, 4, 3⟩ (denote cache_40), placeRow ⟨333, 0, 2, 4⟩ (denote cache_333), placeRow ⟨120, 1, 3, 3⟩ (denote cache_120), placeRow ⟨161, 0, 4, 2⟩ (denote cache_161)] = denote cache_372
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_372

theorem verified_row_373 : fork [place ⟨156, 2, 7, 4⟩ cache_156, place ⟨226, 4, 3, 5⟩ cache_226, place ⟨80, 0, 5, 4⟩ cache_80, place ⟨327, 0, 5, 5⟩ cache_327, place ⟨156, 6, 3, 4⟩ cache_156] = cache_373 := by
  decide +kernel

theorem load_entry_373 : entryAt 373 = entry_373 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_373 : CacheEquation 373 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(373 < 6)), load_entry_373]
  change forkRow [placeRow ⟨156, 2, 7, 4⟩ (denote cache_156), placeRow ⟨226, 4, 3, 5⟩ (denote cache_226), placeRow ⟨80, 0, 5, 4⟩ (denote cache_80), placeRow ⟨327, 0, 5, 5⟩ (denote cache_327), placeRow ⟨156, 6, 3, 4⟩ (denote cache_156)] = denote cache_373
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_373

theorem verified_row_374 : fork [place ⟨65, 4, 3, 4⟩ cache_65, place ⟨335, 0, 7, 4⟩ cache_335, place ⟨24, 2, 7, 3⟩ cache_24, place ⟨163, 4, 3, 4⟩ cache_163] = cache_374 := by
  decide +kernel

theorem load_entry_374 : entryAt 374 = entry_374 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_374 : CacheEquation 374 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(374 < 6)), load_entry_374]
  change forkRow [placeRow ⟨65, 4, 3, 4⟩ (denote cache_65), placeRow ⟨335, 0, 7, 4⟩ (denote cache_335), placeRow ⟨24, 2, 7, 3⟩ (denote cache_24), placeRow ⟨163, 4, 3, 4⟩ (denote cache_163)] = denote cache_374
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_374

theorem verified_row_375 : fork [place ⟨24, 3, 3, 6⟩ cache_24, place ⟨327, 6, 3, 3⟩ cache_327] = cache_375 := by
  decide +kernel

theorem load_entry_375 : entryAt 375 = entry_375 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_375 : CacheEquation 375 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(375 < 6)), load_entry_375]
  change forkRow [placeRow ⟨24, 3, 3, 6⟩ (denote cache_24), placeRow ⟨327, 6, 3, 3⟩ (denote cache_327)] = denote cache_375
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_375

theorem verified_row_376 : fork [place ⟨162, 1, 5, 4⟩ cache_162, place ⟨285, 3, 1, 3⟩ cache_285] = cache_376 := by
  decide +kernel

theorem load_entry_376 : entryAt 376 = entry_376 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_376 : CacheEquation 376 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(376 < 6)), load_entry_376]
  change forkRow [placeRow ⟨162, 1, 5, 4⟩ (denote cache_162), placeRow ⟨285, 3, 1, 3⟩ (denote cache_285)] = denote cache_376
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_376

theorem verified_row_377 : fork [place ⟨29, 3, 3, 0⟩ cache_29, place ⟨362, 0, 7, 2⟩ cache_362] = cache_377 := by
  decide +kernel

theorem load_entry_377 : entryAt 377 = entry_377 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_377 : CacheEquation 377 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(377 < 6)), load_entry_377]
  change forkRow [placeRow ⟨29, 3, 3, 0⟩ (denote cache_29), placeRow ⟨362, 0, 7, 2⟩ (denote cache_362)] = denote cache_377
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_377

theorem verified_row_378 : fork [place ⟨295, 0, 5, 4⟩ cache_295, place ⟨176, 4, 1, 4⟩ cache_176, place ⟨183, 4, 1, 4⟩ cache_183, place ⟨172, 6, 1, 4⟩ cache_172, place ⟨294, 4, 1, 4⟩ cache_294] = cache_378 := by
  decide +kernel

theorem load_entry_378 : entryAt 378 = entry_378 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_378 : CacheEquation 378 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(378 < 6)), load_entry_378]
  change forkRow [placeRow ⟨295, 0, 5, 4⟩ (denote cache_295), placeRow ⟨176, 4, 1, 4⟩ (denote cache_176), placeRow ⟨183, 4, 1, 4⟩ (denote cache_183), placeRow ⟨172, 6, 1, 4⟩ (denote cache_172), placeRow ⟨294, 4, 1, 4⟩ (denote cache_294)] = denote cache_378
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_378

theorem verified_row_379 : fork [place ⟨63, 0, 3, 5⟩ cache_63, place ⟨64, 1, 3, 1⟩ cache_64, place ⟨55, 3, 4, 5⟩ cache_55, place ⟨368, 0, 5, 4⟩ cache_368] = cache_379 := by
  decide +kernel

theorem load_entry_379 : entryAt 379 = entry_379 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_379 : CacheEquation 379 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(379 < 6)), load_entry_379]
  change forkRow [placeRow ⟨63, 0, 3, 5⟩ (denote cache_63), placeRow ⟨64, 1, 3, 1⟩ (denote cache_64), placeRow ⟨55, 3, 4, 5⟩ (denote cache_55), placeRow ⟨368, 0, 5, 4⟩ (denote cache_368)] = denote cache_379
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_379

theorem verified_row_380 : fork [place ⟨101, 4, 2, 5⟩ cache_101, place ⟨271, 0, 2, 5⟩ cache_271, place ⟨223, 0, 5, 4⟩ cache_223, place ⟨192, 3, 1, 4⟩ cache_192] = cache_380 := by
  decide +kernel

theorem load_entry_380 : entryAt 380 = entry_380 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_380 : CacheEquation 380 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(380 < 6)), load_entry_380]
  change forkRow [placeRow ⟨101, 4, 2, 5⟩ (denote cache_101), placeRow ⟨271, 0, 2, 5⟩ (denote cache_271), placeRow ⟨223, 0, 5, 4⟩ (denote cache_223), placeRow ⟨192, 3, 1, 4⟩ (denote cache_192)] = denote cache_380
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_380

theorem verified_row_381 : fork [place ⟨211, 6, 3, 4⟩ cache_211, place ⟨24, 0, 7, 5⟩ cache_24, place ⟨163, 4, 3, 4⟩ cache_163, place ⟨341, 0, 7, 4⟩ cache_341] = cache_381 := by
  decide +kernel

theorem load_entry_381 : entryAt 381 = entry_381 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_381 : CacheEquation 381 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(381 < 6)), load_entry_381]
  change forkRow [placeRow ⟨211, 6, 3, 4⟩ (denote cache_211), placeRow ⟨24, 0, 7, 5⟩ (denote cache_24), placeRow ⟨163, 4, 3, 4⟩ (denote cache_163), placeRow ⟨341, 0, 7, 4⟩ (denote cache_341)] = denote cache_381
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_381

theorem verified_row_382 : fork [place ⟨124, 1, 5, 3⟩ cache_124, place ⟨2, 7, 4, 3⟩ cache_2] = cache_382 := by
  decide +kernel

theorem load_entry_382 : entryAt 382 = entry_382 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_382 : CacheEquation 382 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(382 < 6)), load_entry_382]
  change forkRow [placeRow ⟨124, 1, 5, 3⟩ (denote cache_124), placeRow ⟨2, 7, 4, 3⟩ (denote cache_2)] = denote cache_382
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_382

theorem verified_row_383 : fork [place ⟨192, 3, 2, 4⟩ cache_192, place ⟨271, 0, 3, 5⟩ cache_271, place ⟨197, 0, 6, 4⟩ cache_197, place ⟨172, 0, 6, 4⟩ cache_172, place ⟨215, 4, 3, 5⟩ cache_215] = cache_383 := by
  decide +kernel

theorem load_entry_383 : entryAt 383 = entry_383 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_383 : CacheEquation 383 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(383 < 6)), load_entry_383]
  change forkRow [placeRow ⟨192, 3, 2, 4⟩ (denote cache_192), placeRow ⟨271, 0, 3, 5⟩ (denote cache_271), placeRow ⟨197, 0, 6, 4⟩ (denote cache_197), placeRow ⟨172, 0, 6, 4⟩ (denote cache_172), placeRow ⟨215, 4, 3, 5⟩ (denote cache_215)] = denote cache_383
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_383

theorem verified_row_384 : fork [place ⟨173, 2, 6, 4⟩ cache_173, place ⟨282, 4, 2, 4⟩ cache_282, place ⟨220, 2, 6, 4⟩ cache_220, place ⟨246, 2, 6, 4⟩ cache_246, place ⟨263, 2, 6, 4⟩ cache_263, place ⟨183, 6, 2, 4⟩ cache_183, place ⟨295, 0, 6, 4⟩ cache_295] = cache_384 := by
  decide +kernel

theorem load_entry_384 : entryAt 384 = entry_384 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_384 : CacheEquation 384 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(384 < 6)), load_entry_384]
  change forkRow [placeRow ⟨173, 2, 6, 4⟩ (denote cache_173), placeRow ⟨282, 4, 2, 4⟩ (denote cache_282), placeRow ⟨220, 2, 6, 4⟩ (denote cache_220), placeRow ⟨246, 2, 6, 4⟩ (denote cache_246), placeRow ⟨263, 2, 6, 4⟩ (denote cache_263), placeRow ⟨183, 6, 2, 4⟩ (denote cache_183), placeRow ⟨295, 0, 6, 4⟩ (denote cache_295)] = denote cache_384
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_384

theorem verified_row_385 : fork [place ⟨63, 1, 5, 3⟩ cache_63, place ⟨64, 2, 1, 5⟩ cache_64, place ⟨55, 0, 5, 4⟩ cache_55, place ⟨369, 4, 1, 5⟩ cache_369] = cache_385 := by
  decide +kernel

theorem load_entry_385 : entryAt 385 = entry_385 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_385 : CacheEquation 385 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(385 < 6)), load_entry_385]
  change forkRow [placeRow ⟨63, 1, 5, 3⟩ (denote cache_63), placeRow ⟨64, 2, 1, 5⟩ (denote cache_64), placeRow ⟨55, 0, 5, 4⟩ (denote cache_55), placeRow ⟨369, 4, 1, 5⟩ (denote cache_369)] = denote cache_385
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_385

theorem verified_row_386 : fork [place ⟨217, 4, 1, 4⟩ cache_217, place ⟨172, 0, 5, 4⟩ cache_172, place ⟨173, 4, 1, 4⟩ cache_173, place ⟨217, 0, 5, 4⟩ cache_217, place ⟨294, 0, 5, 4⟩ cache_294, place ⟨294, 4, 1, 4⟩ cache_294] = cache_386 := by
  decide +kernel

theorem load_entry_386 : entryAt 386 = entry_386 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_386 : CacheEquation 386 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(386 < 6)), load_entry_386]
  change forkRow [placeRow ⟨217, 4, 1, 4⟩ (denote cache_217), placeRow ⟨172, 0, 5, 4⟩ (denote cache_172), placeRow ⟨173, 4, 1, 4⟩ (denote cache_173), placeRow ⟨217, 0, 5, 4⟩ (denote cache_217), placeRow ⟨294, 0, 5, 4⟩ (denote cache_294), placeRow ⟨294, 4, 1, 4⟩ (denote cache_294)] = denote cache_386
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_386

theorem verified_row_387 : fork [place ⟨14, 1, 4, 6⟩ cache_14, place ⟨370, 0, 5, 4⟩ cache_370] = cache_387 := by
  decide +kernel

theorem load_entry_387 : entryAt 387 = entry_387 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_387 : CacheEquation 387 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(387 < 6)), load_entry_387]
  change forkRow [placeRow ⟨14, 1, 4, 6⟩ (denote cache_14), placeRow ⟨370, 0, 5, 4⟩ (denote cache_370)] = denote cache_387
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_387

theorem verified_row_388 : fork [place ⟨6, 3, 4, 5⟩ cache_6, place ⟨374, 0, 3, 4⟩ cache_374] = cache_388 := by
  decide +kernel

theorem load_entry_388 : entryAt 388 = entry_388 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_388 : CacheEquation 388 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(388 < 6)), load_entry_388]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (denote cache_6), placeRow ⟨374, 0, 3, 4⟩ (denote cache_374)] = denote cache_388
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_388

theorem verified_row_389 : fork [place ⟨197, 5, 4, 1⟩ cache_197, place ⟨215, 7, 3, 2⟩ cache_215, place ⟨271, 3, 3, 2⟩ cache_271, place ⟨236, 0, 5, 5⟩ cache_236, place ⟨192, 6, 4, 1⟩ cache_192] = cache_389 := by
  decide +kernel

theorem load_entry_389 : entryAt 389 = entry_389 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_389 : CacheEquation 389 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(389 < 6)), load_entry_389]
  change forkRow [placeRow ⟨197, 5, 4, 1⟩ (denote cache_197), placeRow ⟨215, 7, 3, 2⟩ (denote cache_215), placeRow ⟨271, 3, 3, 2⟩ (denote cache_271), placeRow ⟨236, 0, 5, 5⟩ (denote cache_236), placeRow ⟨192, 6, 4, 1⟩ (denote cache_192)] = denote cache_389
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_389

theorem verified_row_390 : fork [place ⟨372, 2, 5, 0⟩ cache_372, place ⟨167, 5, 4, 1⟩ cache_167, place ⟨12, 7, 3, 1⟩ cache_12] = cache_390 := by
  decide +kernel

theorem load_entry_390 : entryAt 390 = entry_390 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_390 : CacheEquation 390 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(390 < 6)), load_entry_390]
  change forkRow [placeRow ⟨372, 2, 5, 0⟩ (denote cache_372), placeRow ⟨167, 5, 4, 1⟩ (denote cache_167), placeRow ⟨12, 7, 3, 1⟩ (denote cache_12)] = denote cache_390
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_390

theorem verified_row_391 : fork [place ⟨6, 5, 5, 1⟩ cache_6, place ⟨388, 0, 3, 5⟩ cache_388] = cache_391 := by
  decide +kernel

theorem load_entry_391 : entryAt 391 = entry_391 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_391 : CacheEquation 391 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(391 < 6)), load_entry_391]
  change forkRow [placeRow ⟨6, 5, 5, 1⟩ (denote cache_6), placeRow ⟨388, 0, 3, 5⟩ (denote cache_388)] = denote cache_391
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_391

theorem verified_row_392 : fork [place ⟨24, 7, 3, 1⟩ cache_24, place ⟨107, 1, 4, 5⟩ cache_107, place ⟨236, 0, 5, 5⟩ cache_236, place ⟨364, 2, 4, 1⟩ cache_364] = cache_392 := by
  decide +kernel

theorem load_entry_392 : entryAt 392 = entry_392 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_392 : CacheEquation 392 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(392 < 6)), load_entry_392]
  change forkRow [placeRow ⟨24, 7, 3, 1⟩ (denote cache_24), placeRow ⟨107, 1, 4, 5⟩ (denote cache_107), placeRow ⟨236, 0, 5, 5⟩ (denote cache_236), placeRow ⟨364, 2, 4, 1⟩ (denote cache_364)] = denote cache_392
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_392

theorem verified_row_393 : fork [place ⟨107, 3, 4, 5⟩ cache_107, place ⟨348, 0, 6, 3⟩ cache_348, place ⟨65, 3, 4, 5⟩ cache_65, place ⟨303, 0, 4, 5⟩ cache_303] = cache_393 := by
  decide +kernel

theorem load_entry_393 : entryAt 393 = entry_393 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_393 : CacheEquation 393 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(393 < 6)), load_entry_393]
  change forkRow [placeRow ⟨107, 3, 4, 5⟩ (denote cache_107), placeRow ⟨348, 0, 6, 3⟩ (denote cache_348), placeRow ⟨65, 3, 4, 5⟩ (denote cache_65), placeRow ⟨303, 0, 4, 5⟩ (denote cache_303)] = denote cache_393
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_393

theorem verified_row_394 : fork [place ⟨226, 4, 1, 4⟩ cache_226, place ⟨226, 0, 5, 4⟩ cache_226, place ⟨327, 4, 3, 4⟩ cache_327, place ⟨327, 6, 3, 3⟩ cache_327, place ⟨226, 6, 1, 3⟩ cache_226, place ⟨226, 2, 5, 3⟩ cache_226] = cache_394 := by
  decide +kernel

theorem load_entry_394 : entryAt 394 = entry_394 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_394 : CacheEquation 394 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(394 < 6)), load_entry_394]
  change forkRow [placeRow ⟨226, 4, 1, 4⟩ (denote cache_226), placeRow ⟨226, 0, 5, 4⟩ (denote cache_226), placeRow ⟨327, 4, 3, 4⟩ (denote cache_327), placeRow ⟨327, 6, 3, 3⟩ (denote cache_327), placeRow ⟨226, 6, 1, 3⟩ (denote cache_226), placeRow ⟨226, 2, 5, 3⟩ (denote cache_226)] = denote cache_394
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_394

theorem verified_row_395 : fork [place ⟨211, 4, 2, 4⟩ cache_211, place ⟨376, 0, 6, 4⟩ cache_376, place ⟨24, 2, 6, 3⟩ cache_24, place ⟨236, 3, 2, 5⟩ cache_236] = cache_395 := by
  decide +kernel

theorem load_entry_395 : entryAt 395 = entry_395 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_395 : CacheEquation 395 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(395 < 6)), load_entry_395]
  change forkRow [placeRow ⟨211, 4, 2, 4⟩ (denote cache_211), placeRow ⟨376, 0, 6, 4⟩ (denote cache_376), placeRow ⟨24, 2, 6, 3⟩ (denote cache_24), placeRow ⟨236, 3, 2, 5⟩ (denote cache_236)] = denote cache_395
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_395

theorem verified_row_396 : fork [place ⟨107, 3, 4, 5⟩ cache_107, place ⟨365, 1, 7, 3⟩ cache_365, place ⟨303, 0, 4, 5⟩ cache_303, place ⟨65, 3, 4, 5⟩ cache_65] = cache_396 := by
  decide +kernel

theorem load_entry_396 : entryAt 396 = entry_396 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_396 : CacheEquation 396 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(396 < 6)), load_entry_396]
  change forkRow [placeRow ⟨107, 3, 4, 5⟩ (denote cache_107), placeRow ⟨365, 1, 7, 3⟩ (denote cache_365), placeRow ⟨303, 0, 4, 5⟩ (denote cache_303), placeRow ⟨65, 3, 4, 5⟩ (denote cache_65)] = denote cache_396
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_396

theorem verified_row_397 : fork [place ⟨24, 3, 4, 5⟩ cache_24, place ⟨374, 0, 3, 4⟩ cache_374, place ⟨65, 5, 5, 1⟩ cache_65] = cache_397 := by
  decide +kernel

theorem load_entry_397 : entryAt 397 = entry_397 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_397 : CacheEquation 397 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(397 < 6)), load_entry_397]
  change forkRow [placeRow ⟨24, 3, 4, 5⟩ (denote cache_24), placeRow ⟨374, 0, 3, 4⟩ (denote cache_374), placeRow ⟨65, 5, 5, 1⟩ (denote cache_65)] = denote cache_397
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_397

theorem verified_row_398 : fork [place ⟨257, 0, 1, 3⟩ cache_257, place ⟨363, 0, 5, 4⟩ cache_363, place ⟨130, 1, 4, 2⟩ cache_130, place ⟨177, 1, 4, 2⟩ cache_177] = cache_398 := by
  decide +kernel

theorem load_entry_398 : entryAt 398 = entry_398 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_398 : CacheEquation 398 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(398 < 6)), load_entry_398]
  change forkRow [placeRow ⟨257, 0, 1, 3⟩ (denote cache_257), placeRow ⟨363, 0, 5, 4⟩ (denote cache_363), placeRow ⟨130, 1, 4, 2⟩ (denote cache_130), placeRow ⟨177, 1, 4, 2⟩ (denote cache_177)] = denote cache_398
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_398

theorem verified_row_399 : fork [place ⟨192, 6, 4, 1⟩ cache_192, place ⟨271, 3, 3, 2⟩ cache_271, place ⟨173, 1, 4, 5⟩ cache_173, place ⟨319, 1, 3, 5⟩ cache_319, place ⟨215, 7, 3, 2⟩ cache_215] = cache_399 := by
  decide +kernel

theorem load_entry_399 : entryAt 399 = entry_399 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_399 : CacheEquation 399 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(399 < 6)), load_entry_399]
  change forkRow [placeRow ⟨192, 6, 4, 1⟩ (denote cache_192), placeRow ⟨271, 3, 3, 2⟩ (denote cache_271), placeRow ⟨173, 1, 4, 5⟩ (denote cache_173), placeRow ⟨319, 1, 3, 5⟩ (denote cache_319), placeRow ⟨215, 7, 3, 2⟩ (denote cache_215)] = denote cache_399
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_399

end SnakyCertificate.Check

end OAI
