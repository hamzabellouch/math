import OAI.Combinatorics.SnakyCertificate.Cache
import OAI.Combinatorics.SnakyCertificate.TableList

namespace OAI

namespace SnakyCertificate.Check

theorem verified_row_160 : fork [place ⟨63, 1, 8, 3⟩ cache_63, place ⟨32, 3, 4, 3⟩ cache_32] = cache_160 := by
  decide +kernel

theorem load_entry_160 : entryAt 160 = entry_160 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_160 : CacheEquation 160 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(160 < 6)), load_entry_160]
  change forkRow [placeRow ⟨63, 1, 8, 3⟩ (denote cache_63), placeRow ⟨32, 3, 4, 3⟩ (denote cache_32)] = denote cache_160
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_160

theorem verified_row_161 : fork [place ⟨15, 1, 4, 5⟩ cache_15, place ⟨86, 0, 5, 4⟩ cache_86] = cache_161 := by
  decide +kernel

theorem load_entry_161 : entryAt 161 = entry_161 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_161 : CacheEquation 161 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(161 < 6)), load_entry_161]
  change forkRow [placeRow ⟨15, 1, 4, 5⟩ (denote cache_15), placeRow ⟨86, 0, 5, 4⟩ (denote cache_86)] = denote cache_161
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_161

theorem verified_row_162 : fork [place ⟨7, 3, 3, 4⟩ cache_7, place ⟨127, 1, 4, 5⟩ cache_127, place ⟨63, 0, 3, 5⟩ cache_63, place ⟨157, 0, 3, 3⟩ cache_157] = cache_162 := by
  decide +kernel

theorem load_entry_162 : entryAt 162 = entry_162 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_162 : CacheEquation 162 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(162 < 6)), load_entry_162]
  change forkRow [placeRow ⟨7, 3, 3, 4⟩ (denote cache_7), placeRow ⟨127, 1, 4, 5⟩ (denote cache_127), placeRow ⟨63, 0, 3, 5⟩ (denote cache_63), placeRow ⟨157, 0, 3, 3⟩ (denote cache_157)] = denote cache_162
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_162

theorem verified_row_163 : fork [place ⟨44, 2, 5, 4⟩ cache_44, place ⟨49, 1, 5, 4⟩ cache_49, place ⟨56, 4, 0, 4⟩ cache_56] = cache_163 := by
  decide +kernel

theorem load_entry_163 : entryAt 163 = entry_163 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_163 : CacheEquation 163 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(163 < 6)), load_entry_163]
  change forkRow [placeRow ⟨44, 2, 5, 4⟩ (denote cache_44), placeRow ⟨49, 1, 5, 4⟩ (denote cache_49), placeRow ⟨56, 4, 0, 4⟩ (denote cache_56)] = denote cache_163
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_163

theorem verified_row_164 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨110, 0, 5, 4⟩ cache_110] = cache_164 := by
  decide +kernel

theorem load_entry_164 : entryAt 164 = entry_164 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_164 : CacheEquation 164 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(164 < 6)), load_entry_164]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨110, 0, 5, 4⟩ (denote cache_110)] = denote cache_164
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_164

theorem verified_row_165 : fork [place ⟨0, 7, 5, 8⟩ cache_0, place ⟨107, 0, 7, 5⟩ cache_107] = cache_165 := by
  decide +kernel

theorem load_entry_165 : entryAt 165 = entry_165 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_165 : CacheEquation 165 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(165 < 6)), load_entry_165]
  change forkRow [placeRow ⟨0, 7, 5, 8⟩ (denote cache_0), placeRow ⟨107, 0, 7, 5⟩ (denote cache_107)] = denote cache_165
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_165

theorem verified_row_166 : fork [place ⟨2, 7, 4, 5⟩ cache_2, place ⟨107, 0, 6, 4⟩ cache_107] = cache_166 := by
  decide +kernel

theorem load_entry_166 : entryAt 166 = entry_166 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_166 : CacheEquation 166 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(166 < 6)), load_entry_166]
  change forkRow [placeRow ⟨2, 7, 4, 5⟩ (denote cache_2), placeRow ⟨107, 0, 6, 4⟩ (denote cache_107)] = denote cache_166
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_166

theorem verified_row_167 : fork [place ⟨57, 0, 5, 4⟩ cache_57, place ⟨57, 4, 0, 4⟩ cache_57] = cache_167 := by
  decide +kernel

theorem load_entry_167 : entryAt 167 = entry_167 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_167 : CacheEquation 167 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(167 < 6)), load_entry_167]
  change forkRow [placeRow ⟨57, 0, 5, 4⟩ (denote cache_57), placeRow ⟨57, 4, 0, 4⟩ (denote cache_57)] = denote cache_167
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_167

theorem verified_row_168 : fork [place ⟨6, 1, 5, 5⟩ cache_6, place ⟨152, 0, 3, 4⟩ cache_152] = cache_168 := by
  decide +kernel

theorem load_entry_168 : entryAt 168 = entry_168 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_168 : CacheEquation 168 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(168 < 6)), load_entry_168]
  change forkRow [placeRow ⟨6, 1, 5, 5⟩ (denote cache_6), placeRow ⟨152, 0, 3, 4⟩ (denote cache_152)] = denote cache_168
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_168

theorem verified_row_169 : fork [place ⟨28, 3, 4, 5⟩ cache_28, place ⟨63, 1, 8, 3⟩ cache_63] = cache_169 := by
  decide +kernel

theorem load_entry_169 : entryAt 169 = entry_169 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_169 : CacheEquation 169 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(169 < 6)), load_entry_169]
  change forkRow [placeRow ⟨28, 3, 4, 5⟩ (denote cache_28), placeRow ⟨63, 1, 8, 3⟩ (denote cache_63)] = denote cache_169
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_169

theorem verified_row_170 : fork [place ⟨4, 6, 1, 3⟩ cache_4, place ⟨127, 2, 5, 4⟩ cache_127] = cache_170 := by
  decide +kernel

theorem load_entry_170 : entryAt 170 = entry_170 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_170 : CacheEquation 170 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(170 < 6)), load_entry_170]
  change forkRow [placeRow ⟨4, 6, 1, 3⟩ (denote cache_4), placeRow ⟨127, 2, 5, 4⟩ (denote cache_127)] = denote cache_170
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_170

theorem verified_row_171 : fork [place ⟨6, 0, 5, 4⟩ cache_6, place ⟨91, 0, 0, 5⟩ cache_91] = cache_171 := by
  decide +kernel

theorem load_entry_171 : entryAt 171 = entry_171 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_171 : CacheEquation 171 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(171 < 6)), load_entry_171]
  change forkRow [placeRow ⟨6, 0, 5, 4⟩ (denote cache_6), placeRow ⟨91, 0, 0, 5⟩ (denote cache_91)] = denote cache_171
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_171

theorem verified_row_172 : fork [place ⟨63, 1, 5, 3⟩ cache_63, place ⟨55, 6, 0, 4⟩ cache_55, place ⟨64, 0, 1, 3⟩ cache_64] = cache_172 := by
  decide +kernel

theorem load_entry_172 : entryAt 172 = entry_172 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_172 : CacheEquation 172 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(172 < 6)), load_entry_172]
  change forkRow [placeRow ⟨63, 1, 5, 3⟩ (denote cache_63), placeRow ⟨55, 6, 0, 4⟩ (denote cache_55), placeRow ⟨64, 0, 1, 3⟩ (denote cache_64)] = denote cache_172
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_172

theorem verified_row_173 : fork [place ⟨63, 1, 5, 3⟩ cache_63, place ⟨64, 6, 4, 5⟩ cache_64, place ⟨55, 6, 0, 4⟩ cache_55] = cache_173 := by
  decide +kernel

theorem load_entry_173 : entryAt 173 = entry_173 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_173 : CacheEquation 173 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(173 < 6)), load_entry_173]
  change forkRow [placeRow ⟨63, 1, 5, 3⟩ (denote cache_63), placeRow ⟨64, 6, 4, 5⟩ (denote cache_64), placeRow ⟨55, 6, 0, 4⟩ (denote cache_55)] = denote cache_173
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_173

theorem verified_row_174 : fork [place ⟨58, 3, 4, 5⟩ cache_58, place ⟨57, 1, 4, 5⟩ cache_57, place ⟨84, 0, 3, 4⟩ cache_84] = cache_174 := by
  decide +kernel

theorem load_entry_174 : entryAt 174 = entry_174 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_174 : CacheEquation 174 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(174 < 6)), load_entry_174]
  change forkRow [placeRow ⟨58, 3, 4, 5⟩ (denote cache_58), placeRow ⟨57, 1, 4, 5⟩ (denote cache_57), placeRow ⟨84, 0, 3, 4⟩ (denote cache_84)] = denote cache_174
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_174

theorem verified_row_175 : fork [place ⟨141, 0, 5, 4⟩ cache_141, place ⟨7, 2, 4, 3⟩ cache_7, place ⟨63, 1, 5, 3⟩ cache_63] = cache_175 := by
  decide +kernel

theorem load_entry_175 : entryAt 175 = entry_175 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_175 : CacheEquation 175 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(175 < 6)), load_entry_175]
  change forkRow [placeRow ⟨141, 0, 5, 4⟩ (denote cache_141), placeRow ⟨7, 2, 4, 3⟩ (denote cache_7), placeRow ⟨63, 1, 5, 3⟩ (denote cache_63)] = denote cache_175
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_175

theorem verified_row_176 : fork [place ⟨63, 1, 5, 3⟩ cache_63, place ⟨64, 6, 4, 5⟩ cache_64, place ⟨55, 2, 5, 4⟩ cache_55] = cache_176 := by
  decide +kernel

theorem load_entry_176 : entryAt 176 = entry_176 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_176 : CacheEquation 176 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(176 < 6)), load_entry_176]
  change forkRow [placeRow ⟨63, 1, 5, 3⟩ (denote cache_63), placeRow ⟨64, 6, 4, 5⟩ (denote cache_64), placeRow ⟨55, 2, 5, 4⟩ (denote cache_55)] = denote cache_176
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_176

theorem verified_row_177 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨136, 3, 5, 4⟩ cache_136] = cache_177 := by
  decide +kernel

theorem load_entry_177 : entryAt 177 = entry_177 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_177 : CacheEquation 177 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(177 < 6)), load_entry_177]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨136, 3, 5, 4⟩ (denote cache_136)] = denote cache_177
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_177

theorem verified_row_178 : fork [place ⟨37, 0, 3, 4⟩ cache_37, place ⟨68, 1, 4, 5⟩ cache_68, place ⟨46, 3, 4, 5⟩ cache_46] = cache_178 := by
  decide +kernel

theorem load_entry_178 : entryAt 178 = entry_178 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_178 : CacheEquation 178 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(178 < 6)), load_entry_178]
  change forkRow [placeRow ⟨37, 0, 3, 4⟩ (denote cache_37), placeRow ⟨68, 1, 4, 5⟩ (denote cache_68), placeRow ⟨46, 3, 4, 5⟩ (denote cache_46)] = denote cache_178
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_178

theorem verified_row_179 : fork [place ⟨6, 6, 0, 3⟩ cache_6, place ⟨148, 5, 5, 4⟩ cache_148] = cache_179 := by
  decide +kernel

theorem load_entry_179 : entryAt 179 = entry_179 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_179 : CacheEquation 179 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(179 < 6)), load_entry_179]
  change forkRow [placeRow ⟨6, 6, 0, 3⟩ (denote cache_6), placeRow ⟨148, 5, 5, 4⟩ (denote cache_148)] = denote cache_179
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_179

theorem verified_row_180 : fork [place ⟨7, 3, 3, 4⟩ cache_7, place ⟨63, 0, 3, 5⟩ cache_63, place ⟨155, 0, 4, 5⟩ cache_155, place ⟨132, 0, 3, 3⟩ cache_132] = cache_180 := by
  decide +kernel

theorem load_entry_180 : entryAt 180 = entry_180 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_180 : CacheEquation 180 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(180 < 6)), load_entry_180]
  change forkRow [placeRow ⟨7, 3, 3, 4⟩ (denote cache_7), placeRow ⟨63, 0, 3, 5⟩ (denote cache_63), placeRow ⟨155, 0, 4, 5⟩ (denote cache_155), placeRow ⟨132, 0, 3, 3⟩ (denote cache_132)] = denote cache_180
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_180

theorem verified_row_181 : fork [place ⟨24, 3, 4, 5⟩ cache_24, place ⟨87, 2, 6, 4⟩ cache_87, place ⟨90, 0, 7, 5⟩ cache_90] = cache_181 := by
  decide +kernel

theorem load_entry_181 : entryAt 181 = entry_181 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_181 : CacheEquation 181 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(181 < 6)), load_entry_181]
  change forkRow [placeRow ⟨24, 3, 4, 5⟩ (denote cache_24), placeRow ⟨87, 2, 6, 4⟩ (denote cache_87), placeRow ⟨90, 0, 7, 5⟩ (denote cache_90)] = denote cache_181
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_181

theorem verified_row_182 : fork [place ⟨12, 2, 7, 3⟩ cache_12, place ⟨139, 0, 7, 4⟩ cache_139] = cache_182 := by
  decide +kernel

theorem load_entry_182 : entryAt 182 = entry_182 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_182 : CacheEquation 182 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(182 < 6)), load_entry_182]
  change forkRow [placeRow ⟨12, 2, 7, 3⟩ (denote cache_12), placeRow ⟨139, 0, 7, 4⟩ (denote cache_139)] = denote cache_182
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_182

theorem verified_row_183 : fork [place ⟨64, 2, 1, 5⟩ cache_64, place ⟨63, 3, 0, 3⟩ cache_63, place ⟨55, 2, 5, 4⟩ cache_55] = cache_183 := by
  decide +kernel

theorem load_entry_183 : entryAt 183 = entry_183 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_183 : CacheEquation 183 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(183 < 6)), load_entry_183]
  change forkRow [placeRow ⟨64, 2, 1, 5⟩ (denote cache_64), placeRow ⟨63, 3, 0, 3⟩ (denote cache_63), placeRow ⟨55, 2, 5, 4⟩ (denote cache_55)] = denote cache_183
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_183

theorem verified_row_184 : fork [place ⟨34, 3, 4, 2⟩ cache_34, place ⟨35, 2, 5, 4⟩ cache_35] = cache_184 := by
  decide +kernel

theorem load_entry_184 : entryAt 184 = entry_184 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_184 : CacheEquation 184 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(184 < 6)), load_entry_184]
  change forkRow [placeRow ⟨34, 3, 4, 2⟩ (denote cache_34), placeRow ⟨35, 2, 5, 4⟩ (denote cache_35)] = denote cache_184
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_184

theorem verified_row_185 : fork [place ⟨44, 3, 4, 5⟩ cache_44, place ⟨49, 0, 4, 5⟩ cache_49, place ⟨84, 0, 3, 4⟩ cache_84] = cache_185 := by
  decide +kernel

theorem load_entry_185 : entryAt 185 = entry_185 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_185 : CacheEquation 185 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(185 < 6)), load_entry_185]
  change forkRow [placeRow ⟨44, 3, 4, 5⟩ (denote cache_44), placeRow ⟨49, 0, 4, 5⟩ (denote cache_49), placeRow ⟨84, 0, 3, 4⟩ (denote cache_84)] = denote cache_185
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_185

theorem verified_row_186 : fork [place ⟨7, 6, 0, 3⟩ cache_7, place ⟨141, 2, 5, 4⟩ cache_141] = cache_186 := by
  decide +kernel

theorem load_entry_186 : entryAt 186 = entry_186 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_186 : CacheEquation 186 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(186 < 6)), load_entry_186]
  change forkRow [placeRow ⟨7, 6, 0, 3⟩ (denote cache_7), placeRow ⟨141, 2, 5, 4⟩ (denote cache_141)] = denote cache_186
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_186

theorem verified_row_187 : fork [place ⟨6, 4, 3, 4⟩ cache_6, place ⟨108, 3, 4, 5⟩ cache_108] = cache_187 := by
  decide +kernel

theorem load_entry_187 : entryAt 187 = entry_187 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_187 : CacheEquation 187 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(187 < 6)), load_entry_187]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (denote cache_6), placeRow ⟨108, 3, 4, 5⟩ (denote cache_108)] = denote cache_187
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_187

theorem verified_row_188 : fork [place ⟨6, 3, 4, 5⟩ cache_6, place ⟨112, 5, 7, 4⟩ cache_112] = cache_188 := by
  decide +kernel

theorem load_entry_188 : entryAt 188 = entry_188 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_188 : CacheEquation 188 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(188 < 6)), load_entry_188]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (denote cache_6), placeRow ⟨112, 5, 7, 4⟩ (denote cache_112)] = denote cache_188
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_188

theorem verified_row_189 : fork [place ⟨12, 0, 5, 4⟩ cache_12, place ⟨86, 4, 1, 4⟩ cache_86] = cache_189 := by
  decide +kernel

theorem load_entry_189 : entryAt 189 = entry_189 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_189 : CacheEquation 189 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(189 < 6)), load_entry_189]
  change forkRow [placeRow ⟨12, 0, 5, 4⟩ (denote cache_12), placeRow ⟨86, 4, 1, 4⟩ (denote cache_86)] = denote cache_189
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_189

theorem verified_row_190 : fork [place ⟨46, 0, 5, 4⟩ cache_46, place ⟨85, 2, 3, 3⟩ cache_85, place ⟨111, 3, 4, 3⟩ cache_111] = cache_190 := by
  decide +kernel

theorem load_entry_190 : entryAt 190 = entry_190 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_190 : CacheEquation 190 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(190 < 6)), load_entry_190]
  change forkRow [placeRow ⟨46, 0, 5, 4⟩ (denote cache_46), placeRow ⟨85, 2, 3, 3⟩ (denote cache_85), placeRow ⟨111, 3, 4, 3⟩ (denote cache_111)] = denote cache_190
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_190

theorem verified_row_191 : fork [place ⟨6, 4, 3, 4⟩ cache_6, place ⟨145, 0, 4, 5⟩ cache_145] = cache_191 := by
  decide +kernel

theorem load_entry_191 : entryAt 191 = entry_191 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_191 : CacheEquation 191 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(191 < 6)), load_entry_191]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (denote cache_6), placeRow ⟨145, 0, 4, 5⟩ (denote cache_145)] = denote cache_191
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_191

theorem verified_row_192 : fork [place ⟨64, 1, 3, 1⟩ cache_64, place ⟨103, 0, 3, 4⟩ cache_103, place ⟨55, 3, 4, 5⟩ cache_55] = cache_192 := by
  decide +kernel

theorem load_entry_192 : entryAt 192 = entry_192 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_192 : CacheEquation 192 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(192 < 6)), load_entry_192]
  change forkRow [placeRow ⟨64, 1, 3, 1⟩ (denote cache_64), placeRow ⟨103, 0, 3, 4⟩ (denote cache_103), placeRow ⟨55, 3, 4, 5⟩ (denote cache_55)] = denote cache_192
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_192

theorem verified_row_193 : fork [place ⟨6, 6, 2, 3⟩ cache_6, place ⟨162, 1, 7, 4⟩ cache_162] = cache_193 := by
  decide +kernel

theorem load_entry_193 : entryAt 193 = entry_193 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_193 : CacheEquation 193 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(193 < 6)), load_entry_193]
  change forkRow [placeRow ⟨6, 6, 2, 3⟩ (denote cache_6), placeRow ⟨162, 1, 7, 4⟩ (denote cache_162)] = denote cache_193
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_193

theorem verified_row_194 : fork [place ⟨0, 0, 0, 3⟩ cache_0, place ⟨146, 4, 2, 5⟩ cache_146] = cache_194 := by
  decide +kernel

theorem load_entry_194 : entryAt 194 = entry_194 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_194 : CacheEquation 194 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(194 < 6)), load_entry_194]
  change forkRow [placeRow ⟨0, 0, 0, 3⟩ (denote cache_0), placeRow ⟨146, 4, 2, 5⟩ (denote cache_146)] = denote cache_194
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_194

theorem verified_row_195 : fork [place ⟨6, 6, 0, 3⟩ cache_6, place ⟨162, 1, 5, 4⟩ cache_162] = cache_195 := by
  decide +kernel

theorem load_entry_195 : entryAt 195 = entry_195 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_195 : CacheEquation 195 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(195 < 6)), load_entry_195]
  change forkRow [placeRow ⟨6, 6, 0, 3⟩ (denote cache_6), placeRow ⟨162, 1, 5, 4⟩ (denote cache_162)] = denote cache_195
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_195

theorem verified_row_196 : fork [place ⟨6, 3, 4, 5⟩ cache_6, place ⟨187, 5, 6, 4⟩ cache_187] = cache_196 := by
  decide +kernel

theorem load_entry_196 : entryAt 196 = entry_196 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_196 : CacheEquation 196 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(196 < 6)), load_entry_196]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (denote cache_6), placeRow ⟨187, 5, 6, 4⟩ (denote cache_187)] = denote cache_196
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_196

theorem verified_row_197 : fork [place ⟨63, 3, 0, 3⟩ cache_63, place ⟨63, 1, 5, 3⟩ cache_63] = cache_197 := by
  decide +kernel

theorem load_entry_197 : entryAt 197 = entry_197 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_197 : CacheEquation 197 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(197 < 6)), load_entry_197]
  change forkRow [placeRow ⟨63, 3, 0, 3⟩ (denote cache_63), placeRow ⟨63, 1, 5, 3⟩ (denote cache_63)] = denote cache_197
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_197

theorem verified_row_198 : fork [place ⟨7, 4, 0, 5⟩ cache_7, place ⟨131, 1, 5, 4⟩ cache_131] = cache_198 := by
  decide +kernel

theorem load_entry_198 : entryAt 198 = entry_198 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_198 : CacheEquation 198 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(198 < 6)), load_entry_198]
  change forkRow [placeRow ⟨7, 4, 0, 5⟩ (denote cache_7), placeRow ⟨131, 1, 5, 4⟩ (denote cache_131)] = denote cache_198
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_198

theorem verified_row_199 : fork [place ⟨55, 1, 4, 5⟩ cache_55, place ⟨64, 3, 5, 1⟩ cache_64, place ⟨84, 0, 3, 4⟩ cache_84] = cache_199 := by
  decide +kernel

theorem load_entry_199 : entryAt 199 = entry_199 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_199 : CacheEquation 199 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(199 < 6)), load_entry_199]
  change forkRow [placeRow ⟨55, 1, 4, 5⟩ (denote cache_55), placeRow ⟨64, 3, 5, 1⟩ (denote cache_64), placeRow ⟨84, 0, 3, 4⟩ (denote cache_84)] = denote cache_199
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_199

end SnakyCertificate.Check

end OAI
