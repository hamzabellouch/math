import OAI.Combinatorics.SnakyCertificate.Cache
import OAI.Combinatorics.SnakyCertificate.TableList

namespace OAI

namespace SnakyCertificate.Check

theorem verified_row_320 : fork [place ⟨19, 1, 4, 3⟩ cache_19, place ⟨267, 2, 6, 4⟩ cache_267, place ⟨115, 7, 4, 3⟩ cache_115] = cache_320 := by
  decide +kernel

theorem load_entry_320 : entryAt 320 = entry_320 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_320 : CacheEquation 320 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(320 < 6)), load_entry_320]
  change forkRow [placeRow ⟨19, 1, 4, 3⟩ (denote cache_19), placeRow ⟨267, 2, 6, 4⟩ (denote cache_267), placeRow ⟨115, 7, 4, 3⟩ (denote cache_115)] = denote cache_320
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_320

theorem verified_row_321 : fork [place ⟨165, 1, 3, 4⟩ cache_165, place ⟨97, 0, 7, 5⟩ cache_97, place ⟨223, 3, 4, 7⟩ cache_223] = cache_321 := by
  decide +kernel

theorem load_entry_321 : entryAt 321 = entry_321 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_321 : CacheEquation 321 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(321 < 6)), load_entry_321]
  change forkRow [placeRow ⟨165, 1, 3, 4⟩ (denote cache_165), placeRow ⟨97, 0, 7, 5⟩ (denote cache_97), placeRow ⟨223, 3, 4, 7⟩ (denote cache_223)] = denote cache_321
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_321

theorem verified_row_322 : fork [place ⟨96, 0, 1, 4⟩ cache_96, place ⟨205, 1, 5, 2⟩ cache_205] = cache_322 := by
  decide +kernel

theorem load_entry_322 : entryAt 322 = entry_322 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_322 : CacheEquation 322 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(322 < 6)), load_entry_322]
  change forkRow [placeRow ⟨96, 0, 1, 4⟩ (denote cache_96), placeRow ⟨205, 1, 5, 2⟩ (denote cache_205)] = denote cache_322
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_322

theorem verified_row_323 : fork [place ⟨165, 6, 4, 5⟩ cache_165, place ⟨278, 0, 1, 4⟩ cache_278, place ⟨25, 1, 4, 5⟩ cache_25] = cache_323 := by
  decide +kernel

theorem load_entry_323 : entryAt 323 = entry_323 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_323 : CacheEquation 323 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(323 < 6)), load_entry_323]
  change forkRow [placeRow ⟨165, 6, 4, 5⟩ (denote cache_165), placeRow ⟨278, 0, 1, 4⟩ (denote cache_278), placeRow ⟨25, 1, 4, 5⟩ (denote cache_25)] = denote cache_323
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_323

theorem verified_row_324 : fork [place ⟨6, 3, 4, 5⟩ cache_6, place ⟨298, 0, 3, 4⟩ cache_298] = cache_324 := by
  decide +kernel

theorem load_entry_324 : entryAt 324 = entry_324 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_324 : CacheEquation 324 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(324 < 6)), load_entry_324]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (denote cache_6), placeRow ⟨298, 0, 3, 4⟩ (denote cache_298)] = denote cache_324
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_324

theorem verified_row_325 : fork [place ⟨25, 0, 6, 5⟩ cache_25, place ⟨313, 1, 6, 4⟩ cache_313, place ⟨24, 2, 6, 3⟩ cache_24] = cache_325 := by
  decide +kernel

theorem load_entry_325 : entryAt 325 = entry_325 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_325 : CacheEquation 325 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(325 < 6)), load_entry_325]
  change forkRow [placeRow ⟨25, 0, 6, 5⟩ (denote cache_25), placeRow ⟨313, 1, 6, 4⟩ (denote cache_313), placeRow ⟨24, 2, 6, 3⟩ (denote cache_24)] = denote cache_325
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_325

theorem verified_row_326 : fork [place ⟨63, 1, 5, 3⟩ cache_63, place ⟨255, 7, 0, 4⟩ cache_255] = cache_326 := by
  decide +kernel

theorem load_entry_326 : entryAt 326 = entry_326 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_326 : CacheEquation 326 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(326 < 6)), load_entry_326]
  change forkRow [placeRow ⟨63, 1, 5, 3⟩ (denote cache_63), placeRow ⟨255, 7, 0, 4⟩ (denote cache_255)] = denote cache_326
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_326

theorem verified_row_327 : fork [place ⟨24, 2, 6, 3⟩ cache_24, place ⟨195, 4, 2, 4⟩ cache_195, place ⟨195, 0, 6, 4⟩ cache_195, place ⟨24, 6, 2, 3⟩ cache_24] = cache_327 := by
  decide +kernel

theorem load_entry_327 : entryAt 327 = entry_327 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_327 : CacheEquation 327 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(327 < 6)), load_entry_327]
  change forkRow [placeRow ⟨24, 2, 6, 3⟩ (denote cache_24), placeRow ⟨195, 4, 2, 4⟩ (denote cache_195), placeRow ⟨195, 0, 6, 4⟩ (denote cache_195), placeRow ⟨24, 6, 2, 3⟩ (denote cache_24)] = denote cache_327
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_327

theorem verified_row_328 : fork [place ⟨49, 0, 4, 5⟩ cache_49, place ⟨44, 3, 4, 5⟩ cache_44, place ⟨285, 0, 3, 4⟩ cache_285] = cache_328 := by
  decide +kernel

theorem load_entry_328 : entryAt 328 = entry_328 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_328 : CacheEquation 328 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(328 < 6)), load_entry_328]
  change forkRow [placeRow ⟨49, 0, 4, 5⟩ (denote cache_49), placeRow ⟨44, 3, 4, 5⟩ (denote cache_44), placeRow ⟨285, 0, 3, 4⟩ (denote cache_285)] = denote cache_328
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_328

theorem verified_row_329 : fork [place ⟨0, 7, 4, 6⟩ cache_0, place ⟨305, 0, 5, 5⟩ cache_305] = cache_329 := by
  decide +kernel

theorem load_entry_329 : entryAt 329 = entry_329 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_329 : CacheEquation 329 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(329 < 6)), load_entry_329]
  change forkRow [placeRow ⟨0, 7, 4, 6⟩ (denote cache_0), placeRow ⟨305, 0, 5, 5⟩ (denote cache_305)] = denote cache_329
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_329

theorem verified_row_330 : fork [place ⟨63, 1, 5, 3⟩ cache_63, place ⟨268, 0, 4, 5⟩ cache_268, place ⟨144, 0, 5, 4⟩ cache_144, place ⟨154, 4, 5, 4⟩ cache_154, place ⟨155, 5, 5, 4⟩ cache_155] = cache_330 := by
  decide +kernel

theorem load_entry_330 : entryAt 330 = entry_330 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_330 : CacheEquation 330 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(330 < 6)), load_entry_330]
  change forkRow [placeRow ⟨63, 1, 5, 3⟩ (denote cache_63), placeRow ⟨268, 0, 4, 5⟩ (denote cache_268), placeRow ⟨144, 0, 5, 4⟩ (denote cache_144), placeRow ⟨154, 4, 5, 4⟩ (denote cache_154), placeRow ⟨155, 5, 5, 4⟩ (denote cache_155)] = denote cache_330
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_330

theorem verified_row_331 : fork [place ⟨113, 0, 1, 4⟩ cache_113, place ⟨15, 0, 3, 4⟩ cache_15, place ⟨298, 4, 4, 5⟩ cache_298, place ⟨90, 2, 5, 4⟩ cache_90] = cache_331 := by
  decide +kernel

theorem load_entry_331 : entryAt 331 = entry_331 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_331 : CacheEquation 331 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(331 < 6)), load_entry_331]
  change forkRow [placeRow ⟨113, 0, 1, 4⟩ (denote cache_113), placeRow ⟨15, 0, 3, 4⟩ (denote cache_15), placeRow ⟨298, 4, 4, 5⟩ (denote cache_298), placeRow ⟨90, 2, 5, 4⟩ (denote cache_90)] = denote cache_331
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_331

theorem verified_row_332 : fork [place ⟨67, 4, 3, 4⟩ cache_67, place ⟨289, 2, 5, 1⟩ cache_289] = cache_332 := by
  decide +kernel

theorem load_entry_332 : entryAt 332 = entry_332 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_332 : CacheEquation 332 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(332 < 6)), load_entry_332]
  change forkRow [placeRow ⟨67, 4, 3, 4⟩ (denote cache_67), placeRow ⟨289, 2, 5, 1⟩ (denote cache_289)] = denote cache_332
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_332

theorem verified_row_333 : fork [place ⟨317, 0, 5, 4⟩ cache_317, place ⟨1, 5, 4, 3⟩ cache_1] = cache_333 := by
  decide +kernel

theorem load_entry_333 : entryAt 333 = entry_333 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_333 : CacheEquation 333 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(333 < 6)), load_entry_333]
  change forkRow [placeRow ⟨317, 0, 5, 4⟩ (denote cache_317), placeRow ⟨1, 5, 4, 3⟩ (denote cache_1)] = denote cache_333
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_333

theorem verified_row_334 : fork [place ⟨67, 6, 3, 2⟩ cache_67, place ⟨289, 0, 5, 5⟩ cache_289] = cache_334 := by
  decide +kernel

theorem load_entry_334 : entryAt 334 = entry_334 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_334 : CacheEquation 334 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(334 < 6)), load_entry_334]
  change forkRow [placeRow ⟨67, 6, 3, 2⟩ (denote cache_67), placeRow ⟨289, 0, 5, 5⟩ (denote cache_289)] = denote cache_334
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_334

theorem verified_row_335 : fork [place ⟨196, 3, 1, 3⟩ cache_196, place ⟨162, 1, 5, 4⟩ cache_162] = cache_335 := by
  decide +kernel

theorem load_entry_335 : entryAt 335 = entry_335 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_335 : CacheEquation 335 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(335 < 6)), load_entry_335]
  change forkRow [placeRow ⟨196, 3, 1, 3⟩ (denote cache_196), placeRow ⟨162, 1, 5, 4⟩ (denote cache_162)] = denote cache_335
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_335

theorem verified_row_336 : fork [place ⟨25, 6, 2, 3⟩ cache_25, place ⟨199, 3, 2, 4⟩ cache_199, place ⟨65, 0, 6, 4⟩ cache_65, place ⟨304, 0, 2, 4⟩ cache_304] = cache_336 := by
  decide +kernel

theorem load_entry_336 : entryAt 336 = entry_336 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_336 : CacheEquation 336 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(336 < 6)), load_entry_336]
  change forkRow [placeRow ⟨25, 6, 2, 3⟩ (denote cache_25), placeRow ⟨199, 3, 2, 4⟩ (denote cache_199), placeRow ⟨65, 0, 6, 4⟩ (denote cache_65), placeRow ⟨304, 0, 2, 4⟩ (denote cache_304)] = denote cache_336
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_336

theorem verified_row_337 : fork [place ⟨107, 3, 3, 7⟩ cache_107, place ⟨230, 2, 1, 5⟩ cache_230] = cache_337 := by
  decide +kernel

theorem load_entry_337 : entryAt 337 = entry_337 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_337 : CacheEquation 337 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(337 < 6)), load_entry_337]
  change forkRow [placeRow ⟨107, 3, 3, 7⟩ (denote cache_107), placeRow ⟨230, 2, 1, 5⟩ (denote cache_230)] = denote cache_337
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_337

theorem verified_row_338 : fork [place ⟨241, 0, 6, 4⟩ cache_241, place ⟨275, 4, 2, 4⟩ cache_275, place ⟨107, 4, 2, 4⟩ cache_107] = cache_338 := by
  decide +kernel

theorem load_entry_338 : entryAt 338 = entry_338 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_338 : CacheEquation 338 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(338 < 6)), load_entry_338]
  change forkRow [placeRow ⟨241, 0, 6, 4⟩ (denote cache_241), placeRow ⟨275, 4, 2, 4⟩ (denote cache_275), placeRow ⟨107, 4, 2, 4⟩ (denote cache_107)] = denote cache_338
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_338

theorem verified_row_339 : fork [place ⟨4, 1, 4, 3⟩ cache_4, place ⟨322, 0, 6, 4⟩ cache_322] = cache_339 := by
  decide +kernel

theorem load_entry_339 : entryAt 339 = entry_339 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_339 : CacheEquation 339 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(339 < 6)), load_entry_339]
  change forkRow [placeRow ⟨4, 1, 4, 3⟩ (denote cache_4), placeRow ⟨322, 0, 6, 4⟩ (denote cache_322)] = denote cache_339
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_339

theorem verified_row_340 : fork [place ⟨25, 3, 3, 6⟩ cache_25, place ⟨300, 4, 4, 6⟩ cache_300, place ⟨24, 3, 3, 6⟩ cache_24] = cache_340 := by
  decide +kernel

theorem load_entry_340 : entryAt 340 = entry_340 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_340 : CacheEquation 340 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(340 < 6)), load_entry_340]
  change forkRow [placeRow ⟨25, 3, 3, 6⟩ (denote cache_25), placeRow ⟨300, 4, 4, 6⟩ (denote cache_300), placeRow ⟨24, 3, 3, 6⟩ (denote cache_24)] = denote cache_340
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_340

theorem verified_row_341 : fork [place ⟨162, 5, 5, 4⟩ cache_162, place ⟨259, 4, 4, 5⟩ cache_259, place ⟨208, 2, 5, 4⟩ cache_208, place ⟨143, 0, 1, 3⟩ cache_143] = cache_341 := by
  decide +kernel

theorem load_entry_341 : entryAt 341 = entry_341 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_341 : CacheEquation 341 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(341 < 6)), load_entry_341]
  change forkRow [placeRow ⟨162, 5, 5, 4⟩ (denote cache_162), placeRow ⟨259, 4, 4, 5⟩ (denote cache_259), placeRow ⟨208, 2, 5, 4⟩ (denote cache_208), placeRow ⟨143, 0, 1, 3⟩ (denote cache_143)] = denote cache_341
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_341

theorem verified_row_342 : fork [place ⟨210, 0, 5, 2⟩ cache_210, place ⟨88, 1, 4, 3⟩ cache_88, place ⟨260, 4, 4, 3⟩ cache_260, place ⟨290, 0, 4, 3⟩ cache_290] = cache_342 := by
  decide +kernel

theorem load_entry_342 : entryAt 342 = entry_342 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_342 : CacheEquation 342 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(342 < 6)), load_entry_342]
  change forkRow [placeRow ⟨210, 0, 5, 2⟩ (denote cache_210), placeRow ⟨88, 1, 4, 3⟩ (denote cache_88), placeRow ⟨260, 4, 4, 3⟩ (denote cache_260), placeRow ⟨290, 0, 4, 3⟩ (denote cache_290)] = denote cache_342
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_342

theorem verified_row_343 : fork [place ⟨0, 5, 4, 5⟩ cache_0, place ⟨250, 0, 5, 4⟩ cache_250] = cache_343 := by
  decide +kernel

theorem load_entry_343 : entryAt 343 = entry_343 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_343 : CacheEquation 343 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(343 < 6)), load_entry_343]
  change forkRow [placeRow ⟨0, 5, 4, 5⟩ (denote cache_0), placeRow ⟨250, 0, 5, 4⟩ (denote cache_250)] = denote cache_343
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_343

theorem verified_row_344 : fork [place ⟨7, 1, 5, 4⟩ cache_7, place ⟨108, 3, 4, 5⟩ cache_108, place ⟨262, 4, 5, 2⟩ cache_262] = cache_344 := by
  decide +kernel

theorem load_entry_344 : entryAt 344 = entry_344 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_344 : CacheEquation 344 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(344 < 6)), load_entry_344]
  change forkRow [placeRow ⟨7, 1, 5, 4⟩ (denote cache_7), placeRow ⟨108, 3, 4, 5⟩ (denote cache_108), placeRow ⟨262, 4, 5, 2⟩ (denote cache_262)] = denote cache_344
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_344

theorem verified_row_345 : fork [place ⟨6, 0, 5, 5⟩ cache_6, place ⟨320, 4, 4, 7⟩ cache_320] = cache_345 := by
  decide +kernel

theorem load_entry_345 : entryAt 345 = entry_345 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_345 : CacheEquation 345 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(345 < 6)), load_entry_345]
  change forkRow [placeRow ⟨6, 0, 5, 5⟩ (denote cache_6), placeRow ⟨320, 4, 4, 7⟩ (denote cache_320)] = denote cache_345
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_345

theorem verified_row_346 : fork [place ⟨60, 1, 4, 3⟩ cache_60, place ⟨255, 0, 1, 4⟩ cache_255, place ⟨276, 0, 1, 4⟩ cache_276] = cache_346 := by
  decide +kernel

theorem load_entry_346 : entryAt 346 = entry_346 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_346 : CacheEquation 346 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(346 < 6)), load_entry_346]
  change forkRow [placeRow ⟨60, 1, 4, 3⟩ (denote cache_60), placeRow ⟨255, 0, 1, 4⟩ (denote cache_255), placeRow ⟨276, 0, 1, 4⟩ (denote cache_276)] = denote cache_346
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_346

theorem verified_row_347 : fork [place ⟨6, 6, 3, 4⟩ cache_6, place ⟨339, 0, 5, 8⟩ cache_339] = cache_347 := by
  decide +kernel

theorem load_entry_347 : entryAt 347 = entry_347 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_347 : CacheEquation 347 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(347 < 6)), load_entry_347]
  change forkRow [placeRow ⟨6, 6, 3, 4⟩ (denote cache_6), placeRow ⟨339, 0, 5, 8⟩ (denote cache_339)] = denote cache_347
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_347

theorem verified_row_348 : fork [place ⟨312, 1, 5, 5⟩ cache_312, place ⟨114, 4, 3, 4⟩ cache_114, place ⟨139, 3, 4, 5⟩ cache_139] = cache_348 := by
  decide +kernel

theorem load_entry_348 : entryAt 348 = entry_348 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_348 : CacheEquation 348 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(348 < 6)), load_entry_348]
  change forkRow [placeRow ⟨312, 1, 5, 5⟩ (denote cache_312), placeRow ⟨114, 4, 3, 4⟩ (denote cache_114), placeRow ⟨139, 3, 4, 5⟩ (denote cache_139)] = denote cache_348
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_348

theorem verified_row_349 : fork [place ⟨14, 1, 4, 5⟩ cache_14, place ⟨17, 1, 4, 5⟩ cache_17, place ⟨332, 0, 3, 4⟩ cache_332] = cache_349 := by
  decide +kernel

theorem load_entry_349 : entryAt 349 = entry_349 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_349 : CacheEquation 349 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(349 < 6)), load_entry_349]
  change forkRow [placeRow ⟨14, 1, 4, 5⟩ (denote cache_14), placeRow ⟨17, 1, 4, 5⟩ (denote cache_17), placeRow ⟨332, 0, 3, 4⟩ (denote cache_332)] = denote cache_349
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_349

theorem verified_row_350 : fork [place ⟨24, 4, 2, 5⟩ cache_24, place ⟨107, 2, 6, 4⟩ cache_107, place ⟨271, 4, 5, 5⟩ cache_271, place ⟨215, 0, 5, 5⟩ cache_215] = cache_350 := by
  decide +kernel

theorem load_entry_350 : entryAt 350 = entry_350 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_350 : CacheEquation 350 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(350 < 6)), load_entry_350]
  change forkRow [placeRow ⟨24, 4, 2, 5⟩ (denote cache_24), placeRow ⟨107, 2, 6, 4⟩ (denote cache_107), placeRow ⟨271, 4, 5, 5⟩ (denote cache_271), placeRow ⟨215, 0, 5, 5⟩ (denote cache_215)] = denote cache_350
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_350

theorem verified_row_351 : fork [place ⟨163, 0, 5, 4⟩ cache_163, place ⟨287, 4, 1, 4⟩ cache_287, place ⟨25, 4, 1, 5⟩ cache_25] = cache_351 := by
  decide +kernel

theorem load_entry_351 : entryAt 351 = entry_351 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_351 : CacheEquation 351 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(351 < 6)), load_entry_351]
  change forkRow [placeRow ⟨163, 0, 5, 4⟩ (denote cache_163), placeRow ⟨287, 4, 1, 4⟩ (denote cache_287), placeRow ⟨25, 4, 1, 5⟩ (denote cache_25)] = denote cache_351
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_351

theorem verified_row_352 : fork [place ⟨214, 0, 4, 5⟩ cache_214, place ⟨91, 0, 3, 4⟩ cache_91, place ⟨63, 0, 3, 5⟩ cache_63, place ⟨344, 0, 4, 5⟩ cache_344, place ⟨180, 4, 4, 5⟩ cache_180] = cache_352 := by
  decide +kernel

theorem load_entry_352 : entryAt 352 = entry_352 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_352 : CacheEquation 352 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(352 < 6)), load_entry_352]
  change forkRow [placeRow ⟨214, 0, 4, 5⟩ (denote cache_214), placeRow ⟨91, 0, 3, 4⟩ (denote cache_91), placeRow ⟨63, 0, 3, 5⟩ (denote cache_63), placeRow ⟨344, 0, 4, 5⟩ (denote cache_344), placeRow ⟨180, 4, 4, 5⟩ (denote cache_180)] = denote cache_352
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_352

theorem verified_row_353 : fork [place ⟨6, 4, 0, 5⟩ cache_6, place ⟨347, 0, 1, 3⟩ cache_347] = cache_353 := by
  decide +kernel

theorem load_entry_353 : entryAt 353 = entry_353 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_353 : CacheEquation 353 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(353 < 6)), load_entry_353]
  change forkRow [placeRow ⟨6, 4, 0, 5⟩ (denote cache_6), placeRow ⟨347, 0, 1, 3⟩ (denote cache_347)] = denote cache_353
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_353

theorem verified_row_354 : fork [place ⟨138, 2, 5, 4⟩ cache_138, place ⟨114, 5, 4, 3⟩ cache_114, place ⟨312, 0, 5, 5⟩ cache_312, place ⟨182, 2, 2, 4⟩ cache_182] = cache_354 := by
  decide +kernel

theorem load_entry_354 : entryAt 354 = entry_354 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_354 : CacheEquation 354 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(354 < 6)), load_entry_354]
  change forkRow [placeRow ⟨138, 2, 5, 4⟩ (denote cache_138), placeRow ⟨114, 5, 4, 3⟩ (denote cache_114), placeRow ⟨312, 0, 5, 5⟩ (denote cache_312), placeRow ⟨182, 2, 2, 4⟩ (denote cache_182)] = denote cache_354
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_354

theorem verified_row_355 : fork [place ⟨12, 2, 7, 3⟩ cache_12, place ⟨167, 0, 7, 4⟩ cache_167, place ⟨342, 0, 6, 6⟩ cache_342] = cache_355 := by
  decide +kernel

theorem load_entry_355 : entryAt 355 = entry_355 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_355 : CacheEquation 355 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(355 < 6)), load_entry_355]
  change forkRow [placeRow ⟨12, 2, 7, 3⟩ (denote cache_12), placeRow ⟨167, 0, 7, 4⟩ (denote cache_167), placeRow ⟨342, 0, 6, 6⟩ (denote cache_342)] = denote cache_355
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_355

theorem verified_row_356 : fork [place ⟨24, 2, 6, 3⟩ cache_24, place ⟨24, 6, 2, 3⟩ cache_24, place ⟨211, 4, 2, 4⟩ cache_211, place ⟨179, 0, 6, 4⟩ cache_179] = cache_356 := by
  decide +kernel

theorem load_entry_356 : entryAt 356 = entry_356 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_356 : CacheEquation 356 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(356 < 6)), load_entry_356]
  change forkRow [placeRow ⟨24, 2, 6, 3⟩ (denote cache_24), placeRow ⟨24, 6, 2, 3⟩ (denote cache_24), placeRow ⟨211, 4, 2, 4⟩ (denote cache_211), placeRow ⟨179, 0, 6, 4⟩ (denote cache_179)] = denote cache_356
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_356

theorem verified_row_357 : fork [place ⟨82, 6, 2, 3⟩ cache_82, place ⟨283, 0, 5, 6⟩ cache_283] = cache_357 := by
  decide +kernel

theorem load_entry_357 : entryAt 357 = entry_357 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_357 : CacheEquation 357 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(357 < 6)), load_entry_357]
  change forkRow [placeRow ⟨82, 6, 2, 3⟩ (denote cache_82), placeRow ⟨283, 0, 5, 6⟩ (denote cache_283)] = denote cache_357
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_357

theorem verified_row_358 : fork [place ⟨6, 0, 5, 4⟩ cache_6, place ⟨346, 0, 4, 6⟩ cache_346] = cache_358 := by
  decide +kernel

theorem load_entry_358 : entryAt 358 = entry_358 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_358 : CacheEquation 358 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(358 < 6)), load_entry_358]
  change forkRow [placeRow ⟨6, 0, 5, 4⟩ (denote cache_6), placeRow ⟨346, 0, 4, 6⟩ (denote cache_346)] = denote cache_358
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_358

theorem verified_row_359 : fork [place ⟨134, 0, 4, 6⟩ cache_134, place ⟨24, 7, 3, 2⟩ cache_24, place ⟨323, 0, 5, 5⟩ cache_323] = cache_359 := by
  decide +kernel

theorem load_entry_359 : entryAt 359 = entry_359 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_359 : CacheEquation 359 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(359 < 6)), load_entry_359]
  change forkRow [placeRow ⟨134, 0, 4, 6⟩ (denote cache_134), placeRow ⟨24, 7, 3, 2⟩ (denote cache_24), placeRow ⟨323, 0, 5, 5⟩ (denote cache_323)] = denote cache_359
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_359

end SnakyCertificate.Check

end OAI
