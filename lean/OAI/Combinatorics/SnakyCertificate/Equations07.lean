import OAI.Combinatorics.SnakyCertificate.Cache
import OAI.Combinatorics.SnakyCertificate.TableList

namespace OAI

namespace SnakyCertificate.Check

theorem verified_row_280 : fork [place ⟨184, 0, 1, 5⟩ cache_184, place ⟨116, 2, 4, 3⟩ cache_116] = cache_280 := by
  decide +kernel

theorem load_entry_280 : entryAt 280 = entry_280 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_280 : CacheEquation 280 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(280 < 6)), load_entry_280]
  change forkRow [placeRow ⟨184, 0, 1, 5⟩ (denote cache_184), placeRow ⟨116, 2, 4, 3⟩ (denote cache_116)] = denote cache_280
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_280

theorem verified_row_281 : fork [place ⟨36, 4, 5, 4⟩ cache_36, place ⟨163, 2, 5, 4⟩ cache_163, place ⟨189, 0, 4, 5⟩ cache_189] = cache_281 := by
  decide +kernel

theorem load_entry_281 : entryAt 281 = entry_281 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_281 : CacheEquation 281 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(281 < 6)), load_entry_281]
  change forkRow [placeRow ⟨36, 4, 5, 4⟩ (denote cache_36), placeRow ⟨163, 2, 5, 4⟩ (denote cache_163), placeRow ⟨189, 0, 4, 5⟩ (denote cache_189)] = denote cache_281
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_281

theorem verified_row_282 : fork [place ⟨56, 0, 5, 4⟩ cache_56, place ⟨64, 0, 1, 3⟩ cache_64, place ⟨55, 0, 5, 4⟩ cache_55, place ⟨265, 0, 1, 3⟩ cache_265] = cache_282 := by
  decide +kernel

theorem load_entry_282 : entryAt 282 = entry_282 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_282 : CacheEquation 282 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(282 < 6)), load_entry_282]
  change forkRow [placeRow ⟨56, 0, 5, 4⟩ (denote cache_56), placeRow ⟨64, 0, 1, 3⟩ (denote cache_64), placeRow ⟨55, 0, 5, 4⟩ (denote cache_55), placeRow ⟨265, 0, 1, 3⟩ (denote cache_265)] = denote cache_282
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_282

theorem verified_row_283 : fork [place ⟨64, 0, 1, 3⟩ cache_64, place ⟨196, 1, 4, 3⟩ cache_196, place ⟨55, 2, 5, 4⟩ cache_55] = cache_283 := by
  decide +kernel

theorem load_entry_283 : entryAt 283 = entry_283 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_283 : CacheEquation 283 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(283 < 6)), load_entry_283]
  change forkRow [placeRow ⟨64, 0, 1, 3⟩ (denote cache_64), placeRow ⟨196, 1, 4, 3⟩ (denote cache_196), placeRow ⟨55, 2, 5, 4⟩ (denote cache_55)] = denote cache_283
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_283

theorem verified_row_284 : fork [place ⟨45, 1, 4, 5⟩ cache_45, place ⟨224, 0, 5, 4⟩ cache_224, place ⟨46, 3, 4, 5⟩ cache_46] = cache_284 := by
  decide +kernel

theorem load_entry_284 : entryAt 284 = entry_284 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_284 : CacheEquation 284 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(284 < 6)), load_entry_284]
  change forkRow [placeRow ⟨45, 1, 4, 5⟩ (denote cache_45), placeRow ⟨224, 0, 5, 4⟩ (denote cache_224), placeRow ⟨46, 3, 4, 5⟩ (denote cache_46)] = denote cache_284
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_284

theorem verified_row_285 : fork [place ⟨6, 3, 4, 5⟩ cache_6, place ⟨273, 0, 6, 4⟩ cache_273] = cache_285 := by
  decide +kernel

theorem load_entry_285 : entryAt 285 = entry_285 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_285 : CacheEquation 285 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(285 < 6)), load_entry_285]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (denote cache_6), placeRow ⟨273, 0, 6, 4⟩ (denote cache_273)] = denote cache_285
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_285

theorem verified_row_286 : fork [place ⟨6, 7, 3, 0⟩ cache_6, place ⟨261, 0, 3, 4⟩ cache_261] = cache_286 := by
  decide +kernel

theorem load_entry_286 : entryAt 286 = entry_286 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_286 : CacheEquation 286 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(286 < 6)), load_entry_286]
  change forkRow [placeRow ⟨6, 7, 3, 0⟩ (denote cache_6), placeRow ⟨261, 0, 3, 4⟩ (denote cache_261)] = denote cache_286
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_286

theorem verified_row_287 : fork [place ⟨64, 0, 1, 3⟩ cache_64, place ⟨55, 0, 5, 4⟩ cache_55, place ⟨56, 0, 5, 4⟩ cache_56, place ⟨264, 4, 4, 5⟩ cache_264] = cache_287 := by
  decide +kernel

theorem load_entry_287 : entryAt 287 = entry_287 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_287 : CacheEquation 287 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(287 < 6)), load_entry_287]
  change forkRow [placeRow ⟨64, 0, 1, 3⟩ (denote cache_64), placeRow ⟨55, 0, 5, 4⟩ (denote cache_55), placeRow ⟨56, 0, 5, 4⟩ (denote cache_56), placeRow ⟨264, 4, 4, 5⟩ (denote cache_264)] = denote cache_287
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_287

theorem verified_row_288 : fork [place ⟨130, 1, 4, 2⟩ cache_130, place ⟨96, 0, 1, 4⟩ cache_96] = cache_288 := by
  decide +kernel

theorem load_entry_288 : entryAt 288 = entry_288 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_288 : CacheEquation 288 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(288 < 6)), load_entry_288]
  change forkRow [placeRow ⟨130, 1, 4, 2⟩ (denote cache_130), placeRow ⟨96, 0, 1, 4⟩ (denote cache_96)] = denote cache_288
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_288

theorem verified_row_289 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨279, 0, 2, 4⟩ cache_279] = cache_289 := by
  decide +kernel

theorem load_entry_289 : entryAt 289 = entry_289 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_289 : CacheEquation 289 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(289 < 6)), load_entry_289]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨279, 0, 2, 4⟩ (denote cache_279)] = denote cache_289
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_289

theorem verified_row_290 : fork [place ⟨67, 2, 5, 2⟩ cache_67, place ⟨231, 4, 5, 5⟩ cache_231] = cache_290 := by
  decide +kernel

theorem load_entry_290 : entryAt 290 = entry_290 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_290 : CacheEquation 290 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(290 < 6)), load_entry_290]
  change forkRow [placeRow ⟨67, 2, 5, 2⟩ (denote cache_67), placeRow ⟨231, 4, 5, 5⟩ (denote cache_231)] = denote cache_290
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_290

theorem verified_row_291 : fork [place ⟨89, 3, 3, 4⟩ cache_89, place ⟨202, 0, 8, 4⟩ cache_202, place ⟨55, 4, 3, 4⟩ cache_55] = cache_291 := by
  decide +kernel

theorem load_entry_291 : entryAt 291 = entry_291 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_291 : CacheEquation 291 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(291 < 6)), load_entry_291]
  change forkRow [placeRow ⟨89, 3, 3, 4⟩ (denote cache_89), placeRow ⟨202, 0, 8, 4⟩ (denote cache_202), placeRow ⟨55, 4, 3, 4⟩ (denote cache_55)] = denote cache_291
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_291

theorem verified_row_292 : fork [place ⟨39, 0, 3, 4⟩ cache_39, place ⟨219, 3, 3, 4⟩ cache_219, place ⟨79, 1, 4, 3⟩ cache_79] = cache_292 := by
  decide +kernel

theorem load_entry_292 : entryAt 292 = entry_292 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_292 : CacheEquation 292 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(292 < 6)), load_entry_292]
  change forkRow [placeRow ⟨39, 0, 3, 4⟩ (denote cache_39), placeRow ⟨219, 3, 3, 4⟩ (denote cache_219), placeRow ⟨79, 1, 4, 3⟩ (denote cache_79)] = denote cache_292
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_292

theorem verified_row_293 : fork [place ⟨2, 7, 4, 3⟩ cache_2, place ⟨280, 0, 5, 4⟩ cache_280] = cache_293 := by
  decide +kernel

theorem load_entry_293 : entryAt 293 = entry_293 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_293 : CacheEquation 293 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(293 < 6)), load_entry_293]
  change forkRow [placeRow ⟨2, 7, 4, 3⟩ (denote cache_2), placeRow ⟨280, 0, 5, 4⟩ (denote cache_280)] = denote cache_293
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_293

theorem verified_row_294 : fork [place ⟨63, 1, 5, 3⟩ cache_63, place ⟨196, 3, 1, 3⟩ cache_196] = cache_294 := by
  decide +kernel

theorem load_entry_294 : entryAt 294 = entry_294 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_294 : CacheEquation 294 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(294 < 6)), load_entry_294]
  change forkRow [placeRow ⟨63, 1, 5, 3⟩ (denote cache_63), placeRow ⟨196, 3, 1, 3⟩ (denote cache_196)] = denote cache_294
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_294

theorem verified_row_295 : fork [place ⟨63, 1, 5, 3⟩ cache_63, place ⟨64, 2, 1, 5⟩ cache_64, place ⟨55, 0, 5, 4⟩ cache_55, place ⟨265, 4, 4, 3⟩ cache_265] = cache_295 := by
  decide +kernel

theorem load_entry_295 : entryAt 295 = entry_295 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_295 : CacheEquation 295 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(295 < 6)), load_entry_295]
  change forkRow [placeRow ⟨63, 1, 5, 3⟩ (denote cache_63), placeRow ⟨64, 2, 1, 5⟩ (denote cache_64), placeRow ⟨55, 0, 5, 4⟩ (denote cache_55), placeRow ⟨265, 4, 4, 3⟩ (denote cache_265)] = denote cache_295
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_295

theorem verified_row_296 : fork [place ⟨107, 1, 4, 5⟩ cache_107, place ⟨209, 3, 3, 4⟩ cache_209, place ⟨65, 1, 4, 5⟩ cache_65] = cache_296 := by
  decide +kernel

theorem load_entry_296 : entryAt 296 = entry_296 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_296 : CacheEquation 296 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(296 < 6)), load_entry_296]
  change forkRow [placeRow ⟨107, 1, 4, 5⟩ (denote cache_107), placeRow ⟨209, 3, 3, 4⟩ (denote cache_209), placeRow ⟨65, 1, 4, 5⟩ (denote cache_65)] = denote cache_296
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_296

theorem verified_row_297 : fork [place ⟨6, 4, 3, 4⟩ cache_6, place ⟨289, 1, 7, 4⟩ cache_289] = cache_297 := by
  decide +kernel

theorem load_entry_297 : entryAt 297 = entry_297 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_297 : CacheEquation 297 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(297 < 6)), load_entry_297]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (denote cache_6), placeRow ⟨289, 1, 7, 4⟩ (denote cache_289)] = denote cache_297
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_297

theorem verified_row_298 : fork [place ⟨24, 2, 7, 3⟩ cache_24, place ⟨24, 6, 3, 3⟩ cache_24, place ⟨107, 4, 3, 4⟩ cache_107, place ⟨195, 0, 7, 4⟩ cache_195] = cache_298 := by
  decide +kernel

theorem load_entry_298 : entryAt 298 = entry_298 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_298 : CacheEquation 298 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(298 < 6)), load_entry_298]
  change forkRow [placeRow ⟨24, 2, 7, 3⟩ (denote cache_24), placeRow ⟨24, 6, 3, 3⟩ (denote cache_24), placeRow ⟨107, 4, 3, 4⟩ (denote cache_107), placeRow ⟨195, 0, 7, 4⟩ (denote cache_195)] = denote cache_298
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_298

theorem verified_row_299 : fork [place ⟨6, 4, 3, 4⟩ cache_6, place ⟨284, 0, 4, 5⟩ cache_284] = cache_299 := by
  decide +kernel

theorem load_entry_299 : entryAt 299 = entry_299 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_299 : CacheEquation 299 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(299 < 6)), load_entry_299]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (denote cache_6), placeRow ⟨284, 0, 4, 5⟩ (denote cache_284)] = denote cache_299
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_299

theorem verified_row_300 : fork [place ⟨64, 3, 5, 1⟩ cache_64, place ⟨240, 2, 5, 1⟩ cache_240, place ⟨55, 3, 4, 5⟩ cache_55] = cache_300 := by
  decide +kernel

theorem load_entry_300 : entryAt 300 = entry_300 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_300 : CacheEquation 300 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(300 < 6)), load_entry_300]
  change forkRow [placeRow ⟨64, 3, 5, 1⟩ (denote cache_64), placeRow ⟨240, 2, 5, 1⟩ (denote cache_240), placeRow ⟨55, 3, 4, 5⟩ (denote cache_55)] = denote cache_300
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_300

theorem verified_row_301 : fork [place ⟨59, 0, 5, 4⟩ cache_59, place ⟨57, 0, 5, 4⟩ cache_57, place ⟨258, 4, 4, 5⟩ cache_258] = cache_301 := by
  decide +kernel

theorem load_entry_301 : entryAt 301 = entry_301 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_301 : CacheEquation 301 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(301 < 6)), load_entry_301]
  change forkRow [placeRow ⟨59, 0, 5, 4⟩ (denote cache_59), placeRow ⟨57, 0, 5, 4⟩ (denote cache_57), placeRow ⟨258, 4, 4, 5⟩ (denote cache_258)] = denote cache_301
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_301

theorem verified_row_302 : fork [place ⟨125, 0, 5, 3⟩ cache_125, place ⟨162, 4, 3, 6⟩ cache_162] = cache_302 := by
  decide +kernel

theorem load_entry_302 : entryAt 302 = entry_302 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_302 : CacheEquation 302 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(302 < 6)), load_entry_302]
  change forkRow [placeRow ⟨125, 0, 5, 3⟩ (denote cache_125), placeRow ⟨162, 4, 3, 6⟩ (denote cache_162)] = denote cache_302
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_302

theorem verified_row_303 : fork [place ⟨49, 4, 4, 5⟩ cache_49, place ⟨44, 1, 4, 5⟩ cache_44, place ⟨63, 0, 3, 5⟩ cache_63, place ⟨261, 0, 3, 4⟩ cache_261] = cache_303 := by
  decide +kernel

theorem load_entry_303 : entryAt 303 = entry_303 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_303 : CacheEquation 303 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(303 < 6)), load_entry_303]
  change forkRow [placeRow ⟨49, 4, 4, 5⟩ (denote cache_49), placeRow ⟨44, 1, 4, 5⟩ (denote cache_44), placeRow ⟨63, 0, 3, 5⟩ (denote cache_63), placeRow ⟨261, 0, 3, 4⟩ (denote cache_261)] = denote cache_303
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_303

theorem verified_row_304 : fork [place ⟨55, 4, 3, 4⟩ cache_55, place ⟨202, 0, 8, 4⟩ cache_202, place ⟨131, 3, 3, 4⟩ cache_131] = cache_304 := by
  decide +kernel

theorem load_entry_304 : entryAt 304 = entry_304 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_304 : CacheEquation 304 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(304 < 6)), load_entry_304]
  change forkRow [placeRow ⟨55, 4, 3, 4⟩ (denote cache_55), placeRow ⟨202, 0, 8, 4⟩ (denote cache_202), placeRow ⟨131, 3, 3, 4⟩ (denote cache_131)] = denote cache_304
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_304

theorem verified_row_305 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨278, 0, 1, 4⟩ cache_278] = cache_305 := by
  decide +kernel

theorem load_entry_305 : entryAt 305 = entry_305 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_305 : CacheEquation 305 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(305 < 6)), load_entry_305]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨278, 0, 1, 4⟩ (denote cache_278)] = denote cache_305
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_305

theorem verified_row_306 : fork [place ⟨4, 1, 4, 3⟩ cache_4, place ⟨288, 0, 6, 4⟩ cache_288] = cache_306 := by
  decide +kernel

theorem load_entry_306 : entryAt 306 = entry_306 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_306 : CacheEquation 306 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(306 < 6)), load_entry_306]
  change forkRow [placeRow ⟨4, 1, 4, 3⟩ (denote cache_4), placeRow ⟨288, 0, 6, 4⟩ (denote cache_288)] = denote cache_306
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_306

theorem verified_row_307 : fork [place ⟨0, 7, 4, 6⟩ cache_0, place ⟨273, 0, 5, 5⟩ cache_273] = cache_307 := by
  decide +kernel

theorem load_entry_307 : entryAt 307 = entry_307 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_307 : CacheEquation 307 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(307 < 6)), load_entry_307]
  change forkRow [placeRow ⟨0, 7, 4, 6⟩ (denote cache_0), placeRow ⟨273, 0, 5, 5⟩ (denote cache_273)] = denote cache_307
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_307

theorem verified_row_308 : fork [place ⟨6, 6, 3, 4⟩ cache_6, place ⟨299, 0, 4, 6⟩ cache_299] = cache_308 := by
  decide +kernel

theorem load_entry_308 : entryAt 308 = entry_308 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_308 : CacheEquation 308 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(308 < 6)), load_entry_308]
  change forkRow [placeRow ⟨6, 6, 3, 4⟩ (denote cache_6), placeRow ⟨299, 0, 4, 6⟩ (denote cache_299)] = denote cache_308
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_308

theorem verified_row_309 : fork [place ⟨28, 6, 3, 4⟩ cache_28, place ⟨268, 1, 5, 7⟩ cache_268] = cache_309 := by
  decide +kernel

theorem load_entry_309 : entryAt 309 = entry_309 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_309 : CacheEquation 309 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(309 < 6)), load_entry_309]
  change forkRow [placeRow ⟨28, 6, 3, 4⟩ (denote cache_28), placeRow ⟨268, 1, 5, 7⟩ (denote cache_268)] = denote cache_309
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_309

theorem verified_row_310 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨281, 0, 5, 3⟩ cache_281] = cache_310 := by
  decide +kernel

theorem load_entry_310 : entryAt 310 = entry_310 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_310 : CacheEquation 310 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(310 < 6)), load_entry_310]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨281, 0, 5, 3⟩ (denote cache_281)] = denote cache_310
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_310

theorem verified_row_311 : fork [place ⟨6, 3, 3, 5⟩ cache_6, place ⟨278, 0, 2, 4⟩ cache_278] = cache_311 := by
  decide +kernel

theorem load_entry_311 : entryAt 311 = entry_311 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_311 : CacheEquation 311 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(311 < 6)), load_entry_311]
  change forkRow [placeRow ⟨6, 3, 3, 5⟩ (denote cache_6), placeRow ⟨278, 0, 2, 4⟩ (denote cache_278)] = denote cache_311
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_311

theorem verified_row_312 : fork [place ⟨9, 2, 5, 4⟩ cache_9, place ⟨272, 0, 4, 5⟩ cache_272] = cache_312 := by
  decide +kernel

theorem load_entry_312 : entryAt 312 = entry_312 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_312 : CacheEquation 312 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(312 < 6)), load_entry_312]
  change forkRow [placeRow ⟨9, 2, 5, 4⟩ (denote cache_9), placeRow ⟨272, 0, 4, 5⟩ (denote cache_272)] = denote cache_312
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_312

theorem verified_row_313 : fork [place ⟨162, 4, 4, 5⟩ cache_162, place ⟨148, 5, 6, 3⟩ cache_148] = cache_313 := by
  decide +kernel

theorem load_entry_313 : entryAt 313 = entry_313 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_313 : CacheEquation 313 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(313 < 6)), load_entry_313]
  change forkRow [placeRow ⟨162, 4, 4, 5⟩ (denote cache_162), placeRow ⟨148, 5, 6, 3⟩ (denote cache_148)] = denote cache_313
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_313

theorem verified_row_314 : fork [place ⟨6, 3, 4, 5⟩ cache_6, place ⟨305, 0, 6, 4⟩ cache_305] = cache_314 := by
  decide +kernel

theorem load_entry_314 : entryAt 314 = entry_314 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_314 : CacheEquation 314 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(314 < 6)), load_entry_314]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (denote cache_6), placeRow ⟨305, 0, 6, 4⟩ (denote cache_305)] = denote cache_314
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_314

theorem verified_row_315 : fork [place ⟨6, 0, 5, 4⟩ cache_6, place ⟨296, 0, 4, 5⟩ cache_296] = cache_315 := by
  decide +kernel

theorem load_entry_315 : entryAt 315 = entry_315 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_315 : CacheEquation 315 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(315 < 6)), load_entry_315]
  change forkRow [placeRow ⟨6, 0, 5, 4⟩ (denote cache_6), placeRow ⟨296, 0, 4, 5⟩ (denote cache_296)] = denote cache_315
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_315

theorem verified_row_316 : fork [place ⟨6, 6, 3, 4⟩ cache_6, place ⟨306, 0, 5, 8⟩ cache_306] = cache_316 := by
  decide +kernel

theorem load_entry_316 : entryAt 316 = entry_316 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_316 : CacheEquation 316 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(316 < 6)), load_entry_316]
  change forkRow [placeRow ⟨6, 6, 3, 4⟩ (denote cache_6), placeRow ⟨306, 0, 5, 8⟩ (denote cache_306)] = denote cache_316
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_316

theorem verified_row_317 : fork [place ⟨263, 2, 6, 4⟩ cache_263, place ⟨26, 3, 4, 3⟩ cache_26, place ⟨99, 0, 5, 5⟩ cache_99] = cache_317 := by
  decide +kernel

theorem load_entry_317 : entryAt 317 = entry_317 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_317 : CacheEquation 317 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(317 < 6)), load_entry_317]
  change forkRow [placeRow ⟨263, 2, 6, 4⟩ (denote cache_263), placeRow ⟨26, 3, 4, 3⟩ (denote cache_26), placeRow ⟨99, 0, 5, 5⟩ (denote cache_99)] = denote cache_317
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_317

theorem verified_row_318 : fork [place ⟨64, 3, 5, 1⟩ cache_64, place ⟨63, 0, 3, 5⟩ cache_63, place ⟨261, 0, 3, 4⟩ cache_261, place ⟨55, 1, 4, 5⟩ cache_55] = cache_318 := by
  decide +kernel

theorem load_entry_318 : entryAt 318 = entry_318 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_318 : CacheEquation 318 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(318 < 6)), load_entry_318]
  change forkRow [placeRow ⟨64, 3, 5, 1⟩ (denote cache_64), placeRow ⟨63, 0, 3, 5⟩ (denote cache_63), placeRow ⟨261, 0, 3, 4⟩ (denote cache_261), placeRow ⟨55, 1, 4, 5⟩ (denote cache_55)] = denote cache_318
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_318

theorem verified_row_319 : fork [place ⟨39, 2, 3, 4⟩ cache_39, place ⟨109, 4, 0, 5⟩ cache_109, place ⟨266, 1, 4, 5⟩ cache_266, place ⟨122, 4, 4, 5⟩ cache_122] = cache_319 := by
  decide +kernel

theorem load_entry_319 : entryAt 319 = entry_319 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_319 : CacheEquation 319 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(319 < 6)), load_entry_319]
  change forkRow [placeRow ⟨39, 2, 3, 4⟩ (denote cache_39), placeRow ⟨109, 4, 0, 5⟩ (denote cache_109), placeRow ⟨266, 1, 4, 5⟩ (denote cache_266), placeRow ⟨122, 4, 4, 5⟩ (denote cache_122)] = denote cache_319
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_319

end SnakyCertificate.Check

end OAI
