import OAI.Combinatorics.SnakyCertificate.Cache
import OAI.Combinatorics.SnakyCertificate.TableList

namespace OAI

namespace SnakyCertificate.Check

theorem verified_row_200 : fork [place ⟨103, 0, 3, 4⟩ cache_103, place ⟨64, 3, 5, 1⟩ cache_64, place ⟨55, 1, 4, 5⟩ cache_55] = cache_200 := by
  decide +kernel

theorem load_entry_200 : entryAt 200 = entry_200 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_200 : CacheEquation 200 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(200 < 6)), load_entry_200]
  change forkRow [placeRow ⟨103, 0, 3, 4⟩ (denote cache_103), placeRow ⟨64, 3, 5, 1⟩ (denote cache_64), placeRow ⟨55, 1, 4, 5⟩ (denote cache_55)] = denote cache_200
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_200

theorem verified_row_201 : fork [place ⟨45, 3, 5, 7⟩ cache_45, place ⟨82, 0, 6, 5⟩ cache_82] = cache_201 := by
  decide +kernel

theorem load_entry_201 : entryAt 201 = entry_201 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_201 : CacheEquation 201 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(201 < 6)), load_entry_201]
  change forkRow [placeRow ⟨45, 3, 5, 7⟩ (denote cache_45), placeRow ⟨82, 0, 6, 5⟩ (denote cache_82)] = denote cache_201
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_201

theorem verified_row_202 : fork [place ⟨150, 0, 5, 4⟩ cache_150, place ⟨7, 0, 4, 5⟩ cache_7, place ⟨108, 0, 5, 4⟩ cache_108] = cache_202 := by
  decide +kernel

theorem load_entry_202 : entryAt 202 = entry_202 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_202 : CacheEquation 202 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(202 < 6)), load_entry_202]
  change forkRow [placeRow ⟨150, 0, 5, 4⟩ (denote cache_150), placeRow ⟨7, 0, 4, 5⟩ (denote cache_7), placeRow ⟨108, 0, 5, 4⟩ (denote cache_108)] = denote cache_202
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_202

theorem verified_row_203 : fork [place ⟨18, 6, 1, 3⟩ cache_18, place ⟨107, 0, 5, 4⟩ cache_107, place ⟨163, 0, 5, 4⟩ cache_163] = cache_203 := by
  decide +kernel

theorem load_entry_203 : entryAt 203 = entry_203 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_203 : CacheEquation 203 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(203 < 6)), load_entry_203]
  change forkRow [placeRow ⟨18, 6, 1, 3⟩ (denote cache_18), placeRow ⟨107, 0, 5, 4⟩ (denote cache_107), placeRow ⟨163, 0, 5, 4⟩ (denote cache_163)] = denote cache_203
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_203

theorem verified_row_204 : fork [place ⟨2, 5, 4, 2⟩ cache_2, place ⟨166, 2, 5, 3⟩ cache_166] = cache_204 := by
  decide +kernel

theorem load_entry_204 : entryAt 204 = entry_204 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_204 : CacheEquation 204 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(204 < 6)), load_entry_204]
  change forkRow [placeRow ⟨2, 5, 4, 2⟩ (denote cache_2), placeRow ⟨166, 2, 5, 3⟩ (denote cache_166)] = denote cache_204
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_204

theorem verified_row_205 : fork [place ⟨4, 1, 4, 3⟩ cache_4, place ⟨168, 0, 3, 4⟩ cache_168] = cache_205 := by
  decide +kernel

theorem load_entry_205 : entryAt 205 = entry_205 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_205 : CacheEquation 205 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(205 < 6)), load_entry_205]
  change forkRow [placeRow ⟨4, 1, 4, 3⟩ (denote cache_4), placeRow ⟨168, 0, 3, 4⟩ (denote cache_168)] = denote cache_205
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_205

theorem verified_row_206 : fork [place ⟨28, 3, 4, 5⟩ cache_28, place ⟨135, 2, 8, 4⟩ cache_135] = cache_206 := by
  decide +kernel

theorem load_entry_206 : entryAt 206 = entry_206 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_206 : CacheEquation 206 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(206 < 6)), load_entry_206]
  change forkRow [placeRow ⟨28, 3, 4, 5⟩ (denote cache_28), placeRow ⟨135, 2, 8, 4⟩ (denote cache_135)] = denote cache_206
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_206

theorem verified_row_207 : fork [place ⟨28, 3, 4, 5⟩ cache_28, place ⟨127, 0, 8, 4⟩ cache_127] = cache_207 := by
  decide +kernel

theorem load_entry_207 : entryAt 207 = entry_207 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_207 : CacheEquation 207 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(207 < 6)), load_entry_207]
  change forkRow [placeRow ⟨28, 3, 4, 5⟩ (denote cache_28), placeRow ⟨127, 0, 8, 4⟩ (denote cache_127)] = denote cache_207
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_207

theorem verified_row_208 : fork [place ⟨7, 4, 0, 5⟩ cache_7, place ⟨127, 0, 5, 4⟩ cache_127] = cache_208 := by
  decide +kernel

theorem load_entry_208 : entryAt 208 = entry_208 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_208 : CacheEquation 208 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(208 < 6)), load_entry_208]
  change forkRow [placeRow ⟨7, 4, 0, 5⟩ (denote cache_7), placeRow ⟨127, 0, 5, 4⟩ (denote cache_127)] = denote cache_208
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_208

theorem verified_row_209 : fork [place ⟨25, 0, 5, 4⟩ cache_25, place ⟨81, 5, 5, 7⟩ cache_81] = cache_209 := by
  decide +kernel

theorem load_entry_209 : entryAt 209 = entry_209 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_209 : CacheEquation 209 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(209 < 6)), load_entry_209]
  change forkRow [placeRow ⟨25, 0, 5, 4⟩ (denote cache_25), placeRow ⟨81, 5, 5, 7⟩ (denote cache_81)] = denote cache_209
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_209

theorem verified_row_210 : fork [place ⟨58, 2, 5, 4⟩ cache_58, place ⟨57, 0, 5, 4⟩ cache_57, place ⟨117, 1, 4, 5⟩ cache_117] = cache_210 := by
  decide +kernel

theorem load_entry_210 : entryAt 210 = entry_210 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_210 : CacheEquation 210 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(210 < 6)), load_entry_210]
  change forkRow [placeRow ⟨58, 2, 5, 4⟩ (denote cache_58), placeRow ⟨57, 0, 5, 4⟩ (denote cache_57), placeRow ⟨117, 1, 4, 5⟩ (denote cache_117)] = denote cache_210
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_210

theorem verified_row_211 : fork [place ⟨49, 5, 5, 4⟩ cache_49, place ⟨6, 6, 0, 3⟩ cache_6] = cache_211 := by
  decide +kernel

theorem load_entry_211 : entryAt 211 = entry_211 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_211 : CacheEquation 211 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(211 < 6)), load_entry_211]
  change forkRow [placeRow ⟨49, 5, 5, 4⟩ (denote cache_49), placeRow ⟨6, 6, 0, 3⟩ (denote cache_6)] = denote cache_211
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_211

theorem verified_row_212 : fork [place ⟨6, 0, 5, 4⟩ cache_6, place ⟨188, 0, 0, 5⟩ cache_188] = cache_212 := by
  decide +kernel

theorem load_entry_212 : entryAt 212 = entry_212 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_212 : CacheEquation 212 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(212 < 6)), load_entry_212]
  change forkRow [placeRow ⟨6, 0, 5, 4⟩ (denote cache_6), placeRow ⟨188, 0, 0, 5⟩ (denote cache_188)] = denote cache_212
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_212

theorem verified_row_213 : fork [place ⟨6, 0, 7, 5⟩ cache_6, place ⟨191, 0, 3, 5⟩ cache_191] = cache_213 := by
  decide +kernel

theorem load_entry_213 : entryAt 213 = entry_213 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_213 : CacheEquation 213 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(213 < 6)), load_entry_213]
  change forkRow [placeRow ⟨6, 0, 7, 5⟩ (denote cache_6), placeRow ⟨191, 0, 3, 5⟩ (denote cache_191)] = denote cache_213
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_213

theorem verified_row_214 : fork [place ⟨7, 3, 3, 4⟩ cache_7, place ⟨108, 3, 4, 5⟩ cache_108, place ⟨95, 0, 5, 2⟩ cache_95] = cache_214 := by
  decide +kernel

theorem load_entry_214 : entryAt 214 = entry_214 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_214 : CacheEquation 214 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(214 < 6)), load_entry_214]
  change forkRow [placeRow ⟨7, 3, 3, 4⟩ (denote cache_7), placeRow ⟨108, 3, 4, 5⟩ (denote cache_108), placeRow ⟨95, 0, 5, 2⟩ (denote cache_95)] = denote cache_214
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_214

theorem verified_row_215 : fork [place ⟨107, 1, 4, 6⟩ cache_107, place ⟨24, 0, 5, 4⟩ cache_24] = cache_215 := by
  decide +kernel

theorem load_entry_215 : entryAt 215 = entry_215 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_215 : CacheEquation 215 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(215 < 6)), load_entry_215]
  change forkRow [placeRow ⟨107, 1, 4, 6⟩ (denote cache_107), placeRow ⟨24, 0, 5, 4⟩ (denote cache_24)] = denote cache_215
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_215

theorem verified_row_216 : fork [place ⟨7, 6, 0, 3⟩ cache_7, place ⟨155, 5, 5, 4⟩ cache_155] = cache_216 := by
  decide +kernel

theorem load_entry_216 : entryAt 216 = entry_216 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_216 : CacheEquation 216 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(216 < 6)), load_entry_216]
  change forkRow [placeRow ⟨7, 6, 0, 3⟩ (denote cache_7), placeRow ⟨155, 5, 5, 4⟩ (denote cache_155)] = denote cache_216
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_216

theorem verified_row_217 : fork [place ⟨111, 1, 1, 3⟩ cache_111, place ⟨55, 4, 0, 4⟩ cache_55, place ⟨64, 0, 1, 3⟩ cache_64] = cache_217 := by
  decide +kernel

theorem load_entry_217 : entryAt 217 = entry_217 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_217 : CacheEquation 217 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(217 < 6)), load_entry_217]
  change forkRow [placeRow ⟨111, 1, 1, 3⟩ (denote cache_111), placeRow ⟨55, 4, 0, 4⟩ (denote cache_55), placeRow ⟨64, 0, 1, 3⟩ (denote cache_64)] = denote cache_217
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_217

theorem verified_row_218 : fork [place ⟨0, 5, 3, 7⟩ cache_0, place ⟨182, 0, 2, 4⟩ cache_182] = cache_218 := by
  decide +kernel

theorem load_entry_218 : entryAt 218 = entry_218 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_218 : CacheEquation 218 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(218 < 6)), load_entry_218]
  change forkRow [placeRow ⟨0, 5, 3, 7⟩ (denote cache_0), placeRow ⟨182, 0, 2, 4⟩ (denote cache_182)] = denote cache_218
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_218

theorem verified_row_219 : fork [place ⟨0, 5, 3, 7⟩ cache_0, place ⟨179, 2, 6, 4⟩ cache_179] = cache_219 := by
  decide +kernel

theorem load_entry_219 : entryAt 219 = entry_219 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_219 : CacheEquation 219 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(219 < 6)), load_entry_219]
  change forkRow [placeRow ⟨0, 5, 3, 7⟩ (denote cache_0), placeRow ⟨179, 2, 6, 4⟩ (denote cache_179)] = denote cache_219
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_219

theorem verified_row_220 : fork [place ⟨56, 4, 0, 4⟩ cache_56, place ⟨63, 1, 5, 3⟩ cache_63, place ⟨144, 2, 5, 4⟩ cache_144, place ⟨154, 6, 5, 4⟩ cache_154, place ⟨155, 1, 5, 4⟩ cache_155] = cache_220 := by
  decide +kernel

theorem load_entry_220 : entryAt 220 = entry_220 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_220 : CacheEquation 220 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(220 < 6)), load_entry_220]
  change forkRow [placeRow ⟨56, 4, 0, 4⟩ (denote cache_56), placeRow ⟨63, 1, 5, 3⟩ (denote cache_63), placeRow ⟨144, 2, 5, 4⟩ (denote cache_144), placeRow ⟨154, 6, 5, 4⟩ (denote cache_154), placeRow ⟨155, 1, 5, 4⟩ (denote cache_155)] = denote cache_220
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_220

theorem verified_row_221 : fork [place ⟨6, 6, 0, 3⟩ cache_6, place ⟨180, 5, 5, 4⟩ cache_180] = cache_221 := by
  decide +kernel

theorem load_entry_221 : entryAt 221 = entry_221 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_221 : CacheEquation 221 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(221 < 6)), load_entry_221]
  change forkRow [placeRow ⟨6, 6, 0, 3⟩ (denote cache_6), placeRow ⟨180, 5, 5, 4⟩ (denote cache_180)] = denote cache_221
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_221

theorem verified_row_222 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨158, 5, 5, 4⟩ cache_158] = cache_222 := by
  decide +kernel

theorem load_entry_222 : entryAt 222 = entry_222 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_222 : CacheEquation 222 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(222 < 6)), load_entry_222]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨158, 5, 5, 4⟩ (denote cache_158)] = denote cache_222
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_222

theorem verified_row_223 : fork [place ⟨63, 1, 5, 3⟩ cache_63, place ⟨135, 2, 5, 4⟩ cache_135, place ⟨128, 0, 3, 3⟩ cache_128, place ⟨111, 3, 4, 3⟩ cache_111, place ⟨127, 0, 5, 4⟩ cache_127] = cache_223 := by
  decide +kernel

theorem load_entry_223 : entryAt 223 = entry_223 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_223 : CacheEquation 223 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(223 < 6)), load_entry_223]
  change forkRow [placeRow ⟨63, 1, 5, 3⟩ (denote cache_63), placeRow ⟨135, 2, 5, 4⟩ (denote cache_135), placeRow ⟨128, 0, 3, 3⟩ (denote cache_128), placeRow ⟨111, 3, 4, 3⟩ (denote cache_111), placeRow ⟨127, 0, 5, 4⟩ (denote cache_127)] = denote cache_223
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_223

theorem verified_row_224 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨212, 0, 6, 3⟩ cache_212] = cache_224 := by
  decide +kernel

theorem load_entry_224 : entryAt 224 = entry_224 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_224 : CacheEquation 224 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(224 < 6)), load_entry_224]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨212, 0, 6, 3⟩ (denote cache_212)] = denote cache_224
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_224

theorem verified_row_225 : fork [place ⟨111, 7, 7, 5⟩ cache_111, place ⟨61, 4, 4, 5⟩ cache_61] = cache_225 := by
  decide +kernel

theorem load_entry_225 : entryAt 225 = entry_225 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_225 : CacheEquation 225 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(225 < 6)), load_entry_225]
  change forkRow [placeRow ⟨111, 7, 7, 5⟩ (denote cache_111), placeRow ⟨61, 4, 4, 5⟩ (denote cache_61)] = denote cache_225
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_225

theorem verified_row_226 : fork [place ⟨10, 6, 0, 3⟩ cache_10, place ⟨203, 0, 5, 4⟩ cache_203, place ⟨33, 0, 2, 3⟩ cache_33, place ⟨193, 0, 2, 4⟩ cache_193] = cache_226 := by
  decide +kernel

theorem load_entry_226 : entryAt 226 = entry_226 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_226 : CacheEquation 226 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(226 < 6)), load_entry_226]
  change forkRow [placeRow ⟨10, 6, 0, 3⟩ (denote cache_10), placeRow ⟨203, 0, 5, 4⟩ (denote cache_203), placeRow ⟨33, 0, 2, 3⟩ (denote cache_33), placeRow ⟨193, 0, 2, 4⟩ (denote cache_193)] = denote cache_226
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_226

theorem verified_row_227 : fork [place ⟨6, 1, 5, 5⟩ cache_6, place ⟨212, 0, 7, 3⟩ cache_212] = cache_227 := by
  decide +kernel

theorem load_entry_227 : entryAt 227 = entry_227 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_227 : CacheEquation 227 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(227 < 6)), load_entry_227]
  change forkRow [placeRow ⟨6, 1, 5, 5⟩ (denote cache_6), placeRow ⟨212, 0, 7, 3⟩ (denote cache_212)] = denote cache_227
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_227

theorem verified_row_228 : fork [place ⟨82, 0, 6, 5⟩ cache_82, place ⟨68, 3, 5, 7⟩ cache_68] = cache_228 := by
  decide +kernel

theorem load_entry_228 : entryAt 228 = entry_228 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_228 : CacheEquation 228 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(228 < 6)), load_entry_228]
  change forkRow [placeRow ⟨82, 0, 6, 5⟩ (denote cache_82), placeRow ⟨68, 3, 5, 7⟩ (denote cache_68)] = denote cache_228
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_228

theorem verified_row_229 : fork [place ⟨171, 0, 7, 3⟩ cache_171, place ⟨45, 1, 4, 5⟩ cache_45, place ⟨46, 3, 4, 5⟩ cache_46] = cache_229 := by
  decide +kernel

theorem load_entry_229 : entryAt 229 = entry_229 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_229 : CacheEquation 229 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(229 < 6)), load_entry_229]
  change forkRow [placeRow ⟨171, 0, 7, 3⟩ (denote cache_171), placeRow ⟨45, 1, 4, 5⟩ (denote cache_45), placeRow ⟨46, 3, 4, 5⟩ (denote cache_46)] = denote cache_229
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_229

theorem verified_row_230 : fork [place ⟨10, 6, 3, 4⟩ cache_10, place ⟨193, 0, 5, 5⟩ cache_193, place ⟨203, 0, 8, 5⟩ cache_203, place ⟨33, 0, 5, 4⟩ cache_33] = cache_230 := by
  decide +kernel

theorem load_entry_230 : entryAt 230 = entry_230 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_230 : CacheEquation 230 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(230 < 6)), load_entry_230]
  change forkRow [placeRow ⟨10, 6, 3, 4⟩ (denote cache_10), placeRow ⟨193, 0, 5, 5⟩ (denote cache_193), placeRow ⟨203, 0, 8, 5⟩ (denote cache_203), placeRow ⟨33, 0, 5, 4⟩ (denote cache_33)] = denote cache_230
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_230

theorem verified_row_231 : fork [place ⟨6, 3, 4, 5⟩ cache_6, place ⟨222, 0, 6, 4⟩ cache_222] = cache_231 := by
  decide +kernel

theorem load_entry_231 : entryAt 231 = entry_231 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_231 : CacheEquation 231 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(231 < 6)), load_entry_231]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (denote cache_6), placeRow ⟨222, 0, 6, 4⟩ (denote cache_222)] = denote cache_231
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_231

theorem verified_row_232 : fork [place ⟨24, 2, 5, 4⟩ cache_24, place ⟨107, 1, 4, 6⟩ cache_107] = cache_232 := by
  decide +kernel

theorem load_entry_232 : entryAt 232 = entry_232 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_232 : CacheEquation 232 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(232 < 6)), load_entry_232]
  change forkRow [placeRow ⟨24, 2, 5, 4⟩ (denote cache_24), placeRow ⟨107, 1, 4, 6⟩ (denote cache_107)] = denote cache_232
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_232

theorem verified_row_233 : fork [place ⟨32, 3, 3, 1⟩ cache_32, place ⟨133, 0, 6, 4⟩ cache_133] = cache_233 := by
  decide +kernel

theorem load_entry_233 : entryAt 233 = entry_233 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_233 : CacheEquation 233 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(233 < 6)), load_entry_233]
  change forkRow [placeRow ⟨32, 3, 3, 1⟩ (denote cache_32), placeRow ⟨133, 0, 6, 4⟩ (denote cache_133)] = denote cache_233
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_233

theorem verified_row_234 : fork [place ⟨180, 4, 4, 5⟩ cache_180, place ⟨37, 0, 3, 4⟩ cache_37, place ⟨129, 0, 5, 3⟩ cache_129, place ⟨63, 0, 3, 5⟩ cache_63] = cache_234 := by
  decide +kernel

theorem load_entry_234 : entryAt 234 = entry_234 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_234 : CacheEquation 234 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(234 < 6)), load_entry_234]
  change forkRow [placeRow ⟨180, 4, 4, 5⟩ (denote cache_180), placeRow ⟨37, 0, 3, 4⟩ (denote cache_37), placeRow ⟨129, 0, 5, 3⟩ (denote cache_129), placeRow ⟨63, 0, 3, 5⟩ (denote cache_63)] = denote cache_234
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_234

theorem verified_row_235 : fork [place ⟨7, 3, 3, 4⟩ cache_7, place ⟨110, 0, 6, 4⟩ cache_110, place ⟨70, 0, 3, 5⟩ cache_70] = cache_235 := by
  decide +kernel

theorem load_entry_235 : entryAt 235 = entry_235 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_235 : CacheEquation 235 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(235 < 6)), load_entry_235]
  change forkRow [placeRow ⟨7, 3, 3, 4⟩ (denote cache_7), placeRow ⟨110, 0, 6, 4⟩ (denote cache_110), placeRow ⟨70, 0, 3, 5⟩ (denote cache_70)] = denote cache_235
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_235

theorem verified_row_236 : fork [place ⟨38, 1, 4, 5⟩ cache_38, place ⟨122, 7, 3, 4⟩ cache_122, place ⟨181, 0, 2, 3⟩ cache_181, place ⟨30, 1, 4, 3⟩ cache_30] = cache_236 := by
  decide +kernel

theorem load_entry_236 : entryAt 236 = entry_236 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_236 : CacheEquation 236 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(236 < 6)), load_entry_236]
  change forkRow [placeRow ⟨38, 1, 4, 5⟩ (denote cache_38), placeRow ⟨122, 7, 3, 4⟩ (denote cache_122), placeRow ⟨181, 0, 2, 3⟩ (denote cache_181), placeRow ⟨30, 1, 4, 3⟩ (denote cache_30)] = denote cache_236
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_236

theorem verified_row_237 : fork [place ⟨6, 3, 4, 5⟩ cache_6, place ⟨172, 0, 7, 4⟩ cache_172] = cache_237 := by
  decide +kernel

theorem load_entry_237 : entryAt 237 = entry_237 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_237 : CacheEquation 237 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(237 < 6)), load_entry_237]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (denote cache_6), placeRow ⟨172, 0, 7, 4⟩ (denote cache_172)] = denote cache_237
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_237

theorem verified_row_238 : fork [place ⟨6, 3, 4, 5⟩ cache_6, place ⟨178, 5, 7, 4⟩ cache_178] = cache_238 := by
  decide +kernel

theorem load_entry_238 : entryAt 238 = entry_238 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_238 : CacheEquation 238 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(238 < 6)), load_entry_238]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (denote cache_6), placeRow ⟨178, 5, 7, 4⟩ (denote cache_178)] = denote cache_238
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_238

theorem verified_row_239 : fork [place ⟨0, 4, 7, 3⟩ cache_0, place ⟨174, 4, 3, 5⟩ cache_174] = cache_239 := by
  decide +kernel

theorem load_entry_239 : entryAt 239 = entry_239 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_239 : CacheEquation 239 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(239 < 6)), load_entry_239]
  change forkRow [placeRow ⟨0, 4, 7, 3⟩ (denote cache_0), placeRow ⟨174, 4, 3, 5⟩ (denote cache_174)] = denote cache_239
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_239

end SnakyCertificate.Check

end OAI
