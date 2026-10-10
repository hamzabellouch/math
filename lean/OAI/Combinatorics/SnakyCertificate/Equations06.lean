import OAI.Combinatorics.SnakyCertificate.Cache
import OAI.Combinatorics.SnakyCertificate.TableList

namespace OAI

namespace SnakyCertificate.Check

theorem verified_row_240 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨237, 0, 2, 4⟩ cache_237] = cache_240 := by
  decide +kernel

theorem load_entry_240 : entryAt 240 = entry_240 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_240 : CacheEquation 240 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(240 < 6)), load_entry_240]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨237, 0, 2, 4⟩ (denote cache_237)] = denote cache_240
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_240

theorem verified_row_241 : fork [place ⟨131, 1, 5, 4⟩ cache_131, place ⟨159, 1, 5, 4⟩ cache_159, place ⟨61, 0, 4, 5⟩ cache_61] = cache_241 := by
  decide +kernel

theorem load_entry_241 : entryAt 241 = entry_241 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_241 : CacheEquation 241 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(241 < 6)), load_entry_241]
  change forkRow [placeRow ⟨131, 1, 5, 4⟩ (denote cache_131), placeRow ⟨159, 1, 5, 4⟩ (denote cache_159), placeRow ⟨61, 0, 4, 5⟩ (denote cache_61)] = denote cache_241
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_241

theorem verified_row_242 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨190, 0, 5, 4⟩ cache_190] = cache_242 := by
  decide +kernel

theorem load_entry_242 : entryAt 242 = entry_242 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_242 : CacheEquation 242 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(242 < 6)), load_entry_242]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨190, 0, 5, 4⟩ (denote cache_190)] = denote cache_242
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_242

theorem verified_row_243 : fork [place ⟨6, 0, 5, 4⟩ cache_6, place ⟨233, 0, 2, 5⟩ cache_233] = cache_243 := by
  decide +kernel

theorem load_entry_243 : entryAt 243 = entry_243 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_243 : CacheEquation 243 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(243 < 6)), load_entry_243]
  change forkRow [placeRow ⟨6, 0, 5, 4⟩ (denote cache_6), placeRow ⟨233, 0, 2, 5⟩ (denote cache_233)] = denote cache_243
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_243

theorem verified_row_244 : fork [place ⟨99, 4, 2, 5⟩ cache_99, place ⟨99, 0, 4, 5⟩ cache_99, place ⟨11, 7, 3, 3⟩ cache_11, place ⟨173, 2, 5, 4⟩ cache_173] = cache_244 := by
  decide +kernel

theorem load_entry_244 : entryAt 244 = entry_244 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_244 : CacheEquation 244 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(244 < 6)), load_entry_244]
  change forkRow [placeRow ⟨99, 4, 2, 5⟩ (denote cache_99), placeRow ⟨99, 0, 4, 5⟩ (denote cache_99), placeRow ⟨11, 7, 3, 3⟩ (denote cache_11), placeRow ⟨173, 2, 5, 4⟩ (denote cache_173)] = denote cache_244
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_244

theorem verified_row_245 : fork [place ⟨64, 0, 1, 3⟩ cache_64, place ⟨175, 4, 0, 4⟩ cache_175, place ⟨143, 6, 4, 5⟩ cache_143, place ⟨186, 6, 0, 4⟩ cache_186] = cache_245 := by
  decide +kernel

theorem load_entry_245 : entryAt 245 = entry_245 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_245 : CacheEquation 245 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(245 < 6)), load_entry_245]
  change forkRow [placeRow ⟨64, 0, 1, 3⟩ (denote cache_64), placeRow ⟨175, 4, 0, 4⟩ (denote cache_175), placeRow ⟨143, 6, 4, 5⟩ (denote cache_143), placeRow ⟨186, 6, 0, 4⟩ (denote cache_186)] = denote cache_245
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_245

theorem verified_row_246 : fork [place ⟨64, 6, 4, 5⟩ cache_64, place ⟨175, 2, 5, 4⟩ cache_175, place ⟨186, 0, 5, 4⟩ cache_186, place ⟨143, 0, 1, 3⟩ cache_143] = cache_246 := by
  decide +kernel

theorem load_entry_246 : entryAt 246 = entry_246 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_246 : CacheEquation 246 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(246 < 6)), load_entry_246]
  change forkRow [placeRow ⟨64, 6, 4, 5⟩ (denote cache_64), placeRow ⟨175, 2, 5, 4⟩ (denote cache_175), placeRow ⟨186, 0, 5, 4⟩ (denote cache_186), placeRow ⟨143, 0, 1, 3⟩ (denote cache_143)] = denote cache_246
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_246

theorem verified_row_247 : fork [place ⟨6, 4, 3, 4⟩ cache_6, place ⟨229, 0, 4, 5⟩ cache_229] = cache_247 := by
  decide +kernel

theorem load_entry_247 : entryAt 247 = entry_247 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_247 : CacheEquation 247 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(247 < 6)), load_entry_247]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (denote cache_6), placeRow ⟨229, 0, 4, 5⟩ (denote cache_229)] = denote cache_247
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_247

theorem verified_row_248 : fork [place ⟨186, 0, 7, 4⟩ cache_186, place ⟨143, 0, 3, 3⟩ cache_143, place ⟨175, 2, 7, 4⟩ cache_175, place ⟨64, 6, 6, 5⟩ cache_64] = cache_248 := by
  decide +kernel

theorem load_entry_248 : entryAt 248 = entry_248 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_248 : CacheEquation 248 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(248 < 6)), load_entry_248]
  change forkRow [placeRow ⟨186, 0, 7, 4⟩ (denote cache_186), placeRow ⟨143, 0, 3, 3⟩ (denote cache_143), placeRow ⟨175, 2, 7, 4⟩ (denote cache_175), placeRow ⟨64, 6, 6, 5⟩ (denote cache_64)] = denote cache_248
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_248

theorem verified_row_249 : fork [place ⟨0, 7, 4, 5⟩ cache_0, place ⟨225, 1, 4, 1⟩ cache_225] = cache_249 := by
  decide +kernel

theorem load_entry_249 : entryAt 249 = entry_249 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_249 : CacheEquation 249 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(249 < 6)), load_entry_249]
  change forkRow [placeRow ⟨0, 7, 4, 5⟩ (denote cache_0), placeRow ⟨225, 1, 4, 1⟩ (denote cache_225)] = denote cache_249
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_249

theorem verified_row_250 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨238, 0, 2, 4⟩ cache_238] = cache_250 := by
  decide +kernel

theorem load_entry_250 : entryAt 250 = entry_250 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_250 : CacheEquation 250 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(250 < 6)), load_entry_250]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨238, 0, 2, 4⟩ (denote cache_238)] = denote cache_250
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_250

theorem verified_row_251 : fork [place ⟨6, 2, 5, 4⟩ cache_6, place ⟨239, 4, 3, 6⟩ cache_239] = cache_251 := by
  decide +kernel

theorem load_entry_251 : entryAt 251 = entry_251 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_251 : CacheEquation 251 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(251 < 6)), load_entry_251]
  change forkRow [placeRow ⟨6, 2, 5, 4⟩ (denote cache_6), placeRow ⟨239, 4, 3, 6⟩ (denote cache_239)] = denote cache_251
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_251

theorem verified_row_252 : fork [place ⟨111, 3, 4, 3⟩ cache_111, place ⟨154, 6, 5, 4⟩ cache_154, place ⟨144, 2, 5, 4⟩ cache_144, place ⟨63, 1, 5, 3⟩ cache_63, place ⟨155, 1, 5, 4⟩ cache_155] = cache_252 := by
  decide +kernel

theorem load_entry_252 : entryAt 252 = entry_252 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_252 : CacheEquation 252 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(252 < 6)), load_entry_252]
  change forkRow [placeRow ⟨111, 3, 4, 3⟩ (denote cache_111), placeRow ⟨154, 6, 5, 4⟩ (denote cache_154), placeRow ⟨144, 2, 5, 4⟩ (denote cache_144), placeRow ⟨63, 1, 5, 3⟩ (denote cache_63), placeRow ⟨155, 1, 5, 4⟩ (denote cache_155)] = denote cache_252
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_252

theorem verified_row_253 : fork [place ⟨29, 3, 3, 0⟩ cache_29, place ⟨177, 1, 6, 2⟩ cache_177] = cache_253 := by
  decide +kernel

theorem load_entry_253 : entryAt 253 = entry_253 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_253 : CacheEquation 253 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(253 < 6)), load_entry_253]
  change forkRow [placeRow ⟨29, 3, 3, 0⟩ (denote cache_29), placeRow ⟨177, 1, 6, 2⟩ (denote cache_177)] = denote cache_253
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_253

theorem verified_row_254 : fork [place ⟨96, 7, 4, 5⟩ cache_96, place ⟨108, 0, 8, 5⟩ cache_108] = cache_254 := by
  decide +kernel

theorem load_entry_254 : entryAt 254 = entry_254 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_254 : CacheEquation 254 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(254 < 6)), load_entry_254]
  change forkRow [placeRow ⟨96, 7, 4, 5⟩ (denote cache_96), placeRow ⟨108, 0, 8, 5⟩ (denote cache_108)] = denote cache_254
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_254

theorem verified_row_255 : fork [place ⟨69, 0, 3, 3⟩ cache_69, place ⟨205, 0, 5, 5⟩ cache_205, place ⟨7, 3, 3, 4⟩ cache_7] = cache_255 := by
  decide +kernel

theorem load_entry_255 : entryAt 255 = entry_255 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_255 : CacheEquation 255 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(255 < 6)), load_entry_255]
  change forkRow [placeRow ⟨69, 0, 3, 3⟩ (denote cache_69), placeRow ⟨205, 0, 5, 5⟩ (denote cache_205), placeRow ⟨7, 3, 3, 4⟩ (denote cache_7)] = denote cache_255
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_255

theorem verified_row_256 : fork [place ⟨0, 5, 4, 5⟩ cache_0, place ⟨231, 0, 3, 4⟩ cache_231] = cache_256 := by
  decide +kernel

theorem load_entry_256 : entryAt 256 = entry_256 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_256 : CacheEquation 256 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(256 < 6)), load_entry_256]
  change forkRow [placeRow ⟨0, 5, 4, 5⟩ (denote cache_0), placeRow ⟨231, 0, 3, 4⟩ (denote cache_231)] = denote cache_256
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_256

theorem verified_row_257 : fork [place ⟨4, 1, 5, 4⟩ cache_4, place ⟨235, 0, 4, 5⟩ cache_235] = cache_257 := by
  decide +kernel

theorem load_entry_257 : entryAt 257 = entry_257 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_257 : CacheEquation 257 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(257 < 6)), load_entry_257]
  change forkRow [placeRow ⟨4, 1, 5, 4⟩ (denote cache_4), placeRow ⟨235, 0, 4, 5⟩ (denote cache_235)] = denote cache_257
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_257

theorem verified_row_258 : fork [place ⟨6, 4, 3, 4⟩ cache_6, place ⟨227, 0, 4, 5⟩ cache_227] = cache_258 := by
  decide +kernel

theorem load_entry_258 : entryAt 258 = entry_258 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_258 : CacheEquation 258 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(258 < 6)), load_entry_258]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (denote cache_6), placeRow ⟨227, 0, 4, 5⟩ (denote cache_227)] = denote cache_258
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_258

theorem verified_row_259 : fork [place ⟨6, 4, 3, 4⟩ cache_6, place ⟨231, 1, 7, 2⟩ cache_231] = cache_259 := by
  decide +kernel

theorem load_entry_259 : entryAt 259 = entry_259 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_259 : CacheEquation 259 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(259 < 6)), load_entry_259]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (denote cache_6), placeRow ⟨231, 1, 7, 2⟩ (denote cache_231)] = denote cache_259
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_259

theorem verified_row_260 : fork [place ⟨0, 5, 4, 6⟩ cache_0, place ⟨231, 0, 3, 5⟩ cache_231] = cache_260 := by
  decide +kernel

theorem load_entry_260 : entryAt 260 = entry_260 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_260 : CacheEquation 260 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(260 < 6)), load_entry_260]
  change forkRow [placeRow ⟨0, 5, 4, 6⟩ (denote cache_0), placeRow ⟨231, 0, 3, 5⟩ (denote cache_231)] = denote cache_260
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_260

theorem verified_row_261 : fork [place ⟨6, 3, 4, 5⟩ cache_6, place ⟨242, 0, 6, 4⟩ cache_242] = cache_261 := by
  decide +kernel

theorem load_entry_261 : entryAt 261 = entry_261 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_261 : CacheEquation 261 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(261 < 6)), load_entry_261]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (denote cache_6), placeRow ⟨242, 0, 6, 4⟩ (denote cache_242)] = denote cache_261
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_261

theorem verified_row_262 : fork [place ⟨0, 7, 5, 7⟩ cache_0, place ⟨213, 0, 3, 4⟩ cache_213] = cache_262 := by
  decide +kernel

theorem load_entry_262 : entryAt 262 = entry_262 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_262 : CacheEquation 262 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(262 < 6)), load_entry_262]
  change forkRow [placeRow ⟨0, 7, 5, 7⟩ (denote cache_0), placeRow ⟨213, 0, 3, 4⟩ (denote cache_213)] = denote cache_262
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_262

theorem verified_row_263 : fork [place ⟨144, 6, 0, 4⟩ cache_144, place ⟨143, 0, 1, 3⟩ cache_143, place ⟨175, 0, 5, 4⟩ cache_175, place ⟨55, 6, 0, 4⟩ cache_55] = cache_263 := by
  decide +kernel

theorem load_entry_263 : entryAt 263 = entry_263 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_263 : CacheEquation 263 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(263 < 6)), load_entry_263]
  change forkRow [placeRow ⟨144, 6, 0, 4⟩ (denote cache_144), placeRow ⟨143, 0, 1, 3⟩ (denote cache_143), placeRow ⟨175, 0, 5, 4⟩ (denote cache_175), placeRow ⟨55, 6, 0, 4⟩ (denote cache_55)] = denote cache_263
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_263

theorem verified_row_264 : fork [place ⟨6, 4, 3, 4⟩ cache_6, place ⟨250, 1, 7, 4⟩ cache_250] = cache_264 := by
  decide +kernel

theorem load_entry_264 : entryAt 264 = entry_264 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_264 : CacheEquation 264 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(264 < 6)), load_entry_264]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (denote cache_6), placeRow ⟨250, 1, 7, 4⟩ (denote cache_250)] = denote cache_264
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_264

theorem verified_row_265 : fork [place ⟨6, 6, 3, 4⟩ cache_6, place ⟨247, 0, 4, 6⟩ cache_247] = cache_265 := by
  decide +kernel

theorem load_entry_265 : entryAt 265 = entry_265 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_265 : CacheEquation 265 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(265 < 6)), load_entry_265]
  change forkRow [placeRow ⟨6, 6, 3, 4⟩ (denote cache_6), placeRow ⟨247, 0, 4, 6⟩ (denote cache_247)] = denote cache_265
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_265

theorem verified_row_266 : fork [place ⟨6, 3, 3, 5⟩ cache_6, place ⟨242, 0, 5, 4⟩ cache_242] = cache_266 := by
  decide +kernel

theorem load_entry_266 : entryAt 266 = entry_266 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_266 : CacheEquation 266 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(266 < 6)), load_entry_266]
  change forkRow [placeRow ⟨6, 3, 3, 5⟩ (denote cache_6), placeRow ⟨242, 0, 5, 4⟩ (denote cache_242)] = denote cache_266
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_266

theorem verified_row_267 : fork [place ⟨175, 4, 1, 4⟩ cache_175, place ⟨144, 2, 6, 4⟩ cache_144, place ⟨55, 2, 6, 4⟩ cache_55, place ⟨143, 4, 5, 3⟩ cache_143] = cache_267 := by
  decide +kernel

theorem load_entry_267 : entryAt 267 = entry_267 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_267 : CacheEquation 267 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(267 < 6)), load_entry_267]
  change forkRow [placeRow ⟨175, 4, 1, 4⟩ (denote cache_175), placeRow ⟨144, 2, 6, 4⟩ (denote cache_144), placeRow ⟨55, 2, 6, 4⟩ (denote cache_55), placeRow ⟨143, 4, 5, 3⟩ (denote cache_143)] = denote cache_267
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_267

theorem verified_row_268 : fork [place ⟨6, 0, 5, 4⟩ cache_6, place ⟨251, 0, 4, 2⟩ cache_251] = cache_268 := by
  decide +kernel

theorem load_entry_268 : entryAt 268 = entry_268 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_268 : CacheEquation 268 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(268 < 6)), load_entry_268]
  change forkRow [placeRow ⟨6, 0, 5, 4⟩ (denote cache_6), placeRow ⟨251, 0, 4, 2⟩ (denote cache_251)] = denote cache_268
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_268

theorem verified_row_269 : fork [place ⟨28, 3, 3, 6⟩ cache_28, place ⟨202, 0, 7, 5⟩ cache_202] = cache_269 := by
  decide +kernel

theorem load_entry_269 : entryAt 269 = entry_269 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_269 : CacheEquation 269 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(269 < 6)), load_entry_269]
  change forkRow [placeRow ⟨28, 3, 3, 6⟩ (denote cache_28), placeRow ⟨202, 0, 7, 5⟩ (denote cache_202)] = denote cache_269
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_269

theorem verified_row_270 : fork [place ⟨63, 0, 3, 7⟩ cache_63, place ⟨6, 7, 3, 2⟩ cache_6] = cache_270 := by
  decide +kernel

theorem load_entry_270 : entryAt 270 = entry_270 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_270 : CacheEquation 270 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(270 < 6)), load_entry_270]
  change forkRow [placeRow ⟨63, 0, 3, 7⟩ (denote cache_63), placeRow ⟨6, 7, 3, 2⟩ (denote cache_6)] = denote cache_270
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_270

theorem verified_row_271 : fork [place ⟨107, 2, 7, 3⟩ cache_107, place ⟨107, 3, 4, 6⟩ cache_107] = cache_271 := by
  decide +kernel

theorem load_entry_271 : entryAt 271 = entry_271 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_271 : CacheEquation 271 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(271 < 6)), load_entry_271]
  change forkRow [placeRow ⟨107, 2, 7, 3⟩ (denote cache_107), placeRow ⟨107, 3, 4, 6⟩ (denote cache_107)] = denote cache_271
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_271

theorem verified_row_272 : fork [place ⟨1, 1, 3, 1⟩ cache_1, place ⟨249, 0, 4, 5⟩ cache_249] = cache_272 := by
  decide +kernel

theorem load_entry_272 : entryAt 272 = entry_272 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_272 : CacheEquation 272 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(272 < 6)), load_entry_272]
  change forkRow [placeRow ⟨1, 1, 3, 1⟩ (denote cache_1), placeRow ⟨249, 0, 4, 5⟩ (denote cache_249)] = denote cache_272
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_272

theorem verified_row_273 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨223, 0, 5, 4⟩ cache_223] = cache_273 := by
  decide +kernel

theorem load_entry_273 : entryAt 273 = entry_273 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_273 : CacheEquation 273 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(273 < 6)), load_entry_273]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨223, 0, 5, 4⟩ (denote cache_223)] = denote cache_273
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_273

theorem verified_row_274 : fork [place ⟨6, 7, 3, 1⟩ cache_6, place ⟨240, 0, 5, 5⟩ cache_240] = cache_274 := by
  decide +kernel

theorem load_entry_274 : entryAt 274 = entry_274 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_274 : CacheEquation 274 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(274 < 6)), load_entry_274]
  change forkRow [placeRow ⟨6, 7, 3, 1⟩ (denote cache_6), placeRow ⟨240, 0, 5, 5⟩ (denote cache_240)] = denote cache_274
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_274

theorem verified_row_275 : fork [place ⟨63, 1, 5, 3⟩ cache_63, place ⟨198, 4, 0, 4⟩ cache_198, place ⟨44, 2, 5, 4⟩ cache_44] = cache_275 := by
  decide +kernel

theorem load_entry_275 : entryAt 275 = entry_275 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_275 : CacheEquation 275 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(275 < 6)), load_entry_275]
  change forkRow [placeRow ⟨63, 1, 5, 3⟩ (denote cache_63), placeRow ⟨198, 4, 0, 4⟩ (denote cache_198), placeRow ⟨44, 2, 5, 4⟩ (denote cache_44)] = denote cache_275
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_275

theorem verified_row_276 : fork [place ⟨7, 3, 3, 4⟩ cache_7, place ⟨177, 0, 5, 4⟩ cache_177, place ⟨63, 0, 3, 5⟩ cache_63] = cache_276 := by
  decide +kernel

theorem load_entry_276 : entryAt 276 = entry_276 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_276 : CacheEquation 276 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(276 < 6)), load_entry_276]
  change forkRow [placeRow ⟨7, 3, 3, 4⟩ (denote cache_7), placeRow ⟨177, 0, 5, 4⟩ (denote cache_177), placeRow ⟨63, 0, 3, 5⟩ (denote cache_63)] = denote cache_276
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_276

theorem verified_row_277 : fork [place ⟨14, 3, 4, 5⟩ cache_14, place ⟨204, 2, 3, 0⟩ cache_204, place ⟨33, 1, 3, 2⟩ cache_33] = cache_277 := by
  decide +kernel

theorem load_entry_277 : entryAt 277 = entry_277 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_277 : CacheEquation 277 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(277 < 6)), load_entry_277]
  change forkRow [placeRow ⟨14, 3, 4, 5⟩ (denote cache_14), placeRow ⟨204, 2, 3, 0⟩ (denote cache_204), placeRow ⟨33, 1, 3, 2⟩ (denote cache_33)] = denote cache_277
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_277

theorem verified_row_278 : fork [place ⟨63, 3, 3, 3⟩ cache_63, place ⟨162, 1, 8, 4⟩ cache_162] = cache_278 := by
  decide +kernel

theorem load_entry_278 : entryAt 278 = entry_278 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_278 : CacheEquation 278 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(278 < 6)), load_entry_278]
  change forkRow [placeRow ⟨63, 3, 3, 3⟩ (denote cache_63), placeRow ⟨162, 1, 8, 4⟩ (denote cache_162)] = denote cache_278
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_278

theorem verified_row_279 : fork [place ⟨6, 3, 4, 5⟩ cache_6, place ⟨234, 5, 7, 4⟩ cache_234] = cache_279 := by
  decide +kernel

theorem load_entry_279 : entryAt 279 = entry_279 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_279 : CacheEquation 279 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(279 < 6)), load_entry_279]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (denote cache_6), placeRow ⟨234, 5, 7, 4⟩ (denote cache_234)] = denote cache_279
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_279

end SnakyCertificate.Check

end OAI
