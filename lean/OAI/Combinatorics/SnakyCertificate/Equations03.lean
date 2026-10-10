import OAI.Combinatorics.SnakyCertificate.Cache
import OAI.Combinatorics.SnakyCertificate.TableList

namespace OAI

namespace SnakyCertificate.Check

theorem verified_row_120 : fork [place ⟨4, 0, 4, 5⟩ cache_4, place ⟨58, 2, 5, 4⟩ cache_58] = cache_120 := by
  decide +kernel

theorem load_entry_120 : entryAt 120 = entry_120 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_120 : CacheEquation 120 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(120 < 6)), load_entry_120]
  change forkRow [placeRow ⟨4, 0, 4, 5⟩ (denote cache_4), placeRow ⟨58, 2, 5, 4⟩ (denote cache_58)] = denote cache_120
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_120

theorem verified_row_121 : fork [place ⟨9, 3, 4, 5⟩ cache_9, place ⟨7, 1, 5, 4⟩ cache_7] = cache_121 := by
  decide +kernel

theorem load_entry_121 : entryAt 121 = entry_121 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_121 : CacheEquation 121 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(121 < 6)), load_entry_121]
  change forkRow [placeRow ⟨9, 3, 4, 5⟩ (denote cache_9), placeRow ⟨7, 1, 5, 4⟩ (denote cache_7)] = denote cache_121
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_121

theorem verified_row_122 : fork [place ⟨6, 6, 3, 3⟩ cache_6, place ⟨105, 1, 4, 5⟩ cache_105] = cache_122 := by
  decide +kernel

theorem load_entry_122 : entryAt 122 = entry_122 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_122 : CacheEquation 122 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(122 < 6)), load_entry_122]
  change forkRow [placeRow ⟨6, 6, 3, 3⟩ (denote cache_6), placeRow ⟨105, 1, 4, 5⟩ (denote cache_105)] = denote cache_122
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_122

theorem verified_row_123 : fork [place ⟨6, 6, 1, 3⟩ cache_6, place ⟨64, 2, 2, 5⟩ cache_64] = cache_123 := by
  decide +kernel

theorem load_entry_123 : entryAt 123 = entry_123 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_123 : CacheEquation 123 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(123 < 6)), load_entry_123]
  change forkRow [placeRow ⟨6, 6, 1, 3⟩ (denote cache_6), placeRow ⟨64, 2, 2, 5⟩ (denote cache_64)] = denote cache_123
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_123

theorem verified_row_124 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨31, 2, 5, 4⟩ cache_31] = cache_124 := by
  decide +kernel

theorem load_entry_124 : entryAt 124 = entry_124 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_124 : CacheEquation 124 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(124 < 6)), load_entry_124]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨31, 2, 5, 4⟩ (denote cache_31)] = denote cache_124
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_124

theorem verified_row_125 : fork [place ⟨3, 0, 4, 3⟩ cache_3, place ⟨31, 2, 4, 5⟩ cache_31] = cache_125 := by
  decide +kernel

theorem load_entry_125 : entryAt 125 = entry_125 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_125 : CacheEquation 125 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(125 < 6)), load_entry_125]
  change forkRow [placeRow ⟨3, 0, 4, 3⟩ (denote cache_3), placeRow ⟨31, 2, 4, 5⟩ (denote cache_31)] = denote cache_125
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_125

theorem verified_row_126 : fork [place ⟨6, 3, 4, 5⟩ cache_6, place ⟨46, 1, 5, 7⟩ cache_46] = cache_126 := by
  decide +kernel

theorem load_entry_126 : entryAt 126 = entry_126 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_126 : CacheEquation 126 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(126 < 6)), load_entry_126]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (denote cache_6), placeRow ⟨46, 1, 5, 7⟩ (denote cache_46)] = denote cache_126
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_126

theorem verified_row_127 : fork [place ⟨7, 0, 4, 5⟩ cache_7, place ⟨44, 2, 5, 4⟩ cache_44] = cache_127 := by
  decide +kernel

theorem load_entry_127 : entryAt 127 = entry_127 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_127 : CacheEquation 127 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(127 < 6)), load_entry_127]
  change forkRow [placeRow ⟨7, 0, 4, 5⟩ (denote cache_7), placeRow ⟨44, 2, 5, 4⟩ (denote cache_44)] = denote cache_127
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_127

theorem verified_row_128 : fork [place ⟨9, 6, 1, 5⟩ cache_9, place ⟨57, 0, 6, 5⟩ cache_57] = cache_128 := by
  decide +kernel

theorem load_entry_128 : entryAt 128 = entry_128 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_128 : CacheEquation 128 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(128 < 6)), load_entry_128]
  change forkRow [placeRow ⟨9, 6, 1, 5⟩ (denote cache_9), placeRow ⟨57, 0, 6, 5⟩ (denote cache_57)] = denote cache_128
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_128

theorem verified_row_129 : fork [place ⟨6, 4, 2, 5⟩ cache_6, place ⟨58, 1, 3, 6⟩ cache_58] = cache_129 := by
  decide +kernel

theorem load_entry_129 : entryAt 129 = entry_129 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_129 : CacheEquation 129 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(129 < 6)), load_entry_129]
  change forkRow [placeRow ⟨6, 4, 2, 5⟩ (denote cache_6), placeRow ⟨58, 1, 3, 6⟩ (denote cache_58)] = denote cache_129
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_129

theorem verified_row_130 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨60, 0, 5, 4⟩ cache_60] = cache_130 := by
  decide +kernel

theorem load_entry_130 : entryAt 130 = entry_130 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_130 : CacheEquation 130 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(130 < 6)), load_entry_130]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨60, 0, 5, 4⟩ (denote cache_60)] = denote cache_130
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_130

theorem verified_row_131 : fork [place ⟨45, 3, 4, 5⟩ cache_45, place ⟨7, 1, 5, 4⟩ cache_7] = cache_131 := by
  decide +kernel

theorem load_entry_131 : entryAt 131 = entry_131 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_131 : CacheEquation 131 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(131 < 6)), load_entry_131]
  change forkRow [placeRow ⟨45, 3, 4, 5⟩ (denote cache_45), placeRow ⟨7, 1, 5, 4⟩ (denote cache_7)] = denote cache_131
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_131

theorem verified_row_132 : fork [place ⟨6, 3, 4, 5⟩ cache_6, place ⟨89, 0, 5, 6⟩ cache_89] = cache_132 := by
  decide +kernel

theorem load_entry_132 : entryAt 132 = entry_132 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_132 : CacheEquation 132 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(132 < 6)), load_entry_132]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (denote cache_6), placeRow ⟨89, 0, 5, 6⟩ (denote cache_89)] = denote cache_132
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_132

theorem verified_row_133 : fork [place ⟨6, 7, 3, 1⟩ cache_6, place ⟨92, 0, 5, 5⟩ cache_92] = cache_133 := by
  decide +kernel

theorem load_entry_133 : entryAt 133 = entry_133 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_133 : CacheEquation 133 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(133 < 6)), load_entry_133]
  change forkRow [placeRow ⟨6, 7, 3, 1⟩ (denote cache_6), placeRow ⟨92, 0, 5, 5⟩ (denote cache_92)] = denote cache_133
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_133

theorem verified_row_134 : fork [place ⟨6, 7, 3, 0⟩ cache_6, place ⟨82, 0, 5, 4⟩ cache_82] = cache_134 := by
  decide +kernel

theorem load_entry_134 : entryAt 134 = entry_134 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_134 : CacheEquation 134 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(134 < 6)), load_entry_134]
  change forkRow [placeRow ⟨6, 7, 3, 0⟩ (denote cache_6), placeRow ⟨82, 0, 5, 4⟩ (denote cache_82)] = denote cache_134
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_134

theorem verified_row_135 : fork [place ⟨7, 0, 4, 5⟩ cache_7, place ⟨75, 4, 2, 5⟩ cache_75, place ⟨44, 0, 5, 4⟩ cache_44] = cache_135 := by
  decide +kernel

theorem load_entry_135 : entryAt 135 = entry_135 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_135 : CacheEquation 135 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(135 < 6)), load_entry_135]
  change forkRow [placeRow ⟨7, 0, 4, 5⟩ (denote cache_7), placeRow ⟨75, 4, 2, 5⟩ (denote cache_75), placeRow ⟨44, 0, 5, 4⟩ (denote cache_44)] = denote cache_135
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_135

theorem verified_row_136 : fork [place ⟨6, 3, 3, 7⟩ cache_6, place ⟨102, 2, 3, 3⟩ cache_102] = cache_136 := by
  decide +kernel

theorem load_entry_136 : entryAt 136 = entry_136 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_136 : CacheEquation 136 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(136 < 6)), load_entry_136]
  change forkRow [placeRow ⟨6, 3, 3, 7⟩ (denote cache_6), placeRow ⟨102, 2, 3, 3⟩ (denote cache_102)] = denote cache_136
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_136

theorem verified_row_137 : fork [place ⟨4, 1, 4, 3⟩ cache_4, place ⟨96, 0, 3, 4⟩ cache_96] = cache_137 := by
  decide +kernel

theorem load_entry_137 : entryAt 137 = entry_137 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_137 : CacheEquation 137 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(137 < 6)), load_entry_137]
  change forkRow [placeRow ⟨4, 1, 4, 3⟩ (denote cache_4), placeRow ⟨96, 0, 3, 4⟩ (denote cache_96)] = denote cache_137
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_137

theorem verified_row_138 : fork [place ⟨27, 0, 5, 4⟩ cache_27, place ⟨10, 1, 4, 7⟩ cache_10] = cache_138 := by
  decide +kernel

theorem load_entry_138 : entryAt 138 = entry_138 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_138 : CacheEquation 138 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(138 < 6)), load_entry_138]
  change forkRow [placeRow ⟨27, 0, 5, 4⟩ (denote cache_27), placeRow ⟨10, 1, 4, 7⟩ (denote cache_10)] = denote cache_138
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_138

theorem verified_row_139 : fork [place ⟨28, 1, 4, 5⟩ cache_28, place ⟨27, 0, 5, 4⟩ cache_27] = cache_139 := by
  decide +kernel

theorem load_entry_139 : entryAt 139 = entry_139 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_139 : CacheEquation 139 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(139 < 6)), load_entry_139]
  change forkRow [placeRow ⟨28, 1, 4, 5⟩ (denote cache_28), placeRow ⟨27, 0, 5, 4⟩ (denote cache_27)] = denote cache_139
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_139

theorem verified_row_140 : fork [place ⟨6, 7, 3, 2⟩ cache_6, place ⟨82, 0, 5, 6⟩ cache_82] = cache_140 := by
  decide +kernel

theorem load_entry_140 : entryAt 140 = entry_140 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_140 : CacheEquation 140 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(140 < 6)), load_entry_140]
  change forkRow [placeRow ⟨6, 7, 3, 2⟩ (denote cache_6), placeRow ⟨82, 0, 5, 6⟩ (denote cache_82)] = denote cache_140
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_140

theorem verified_row_141 : fork [place ⟨7, 0, 4, 5⟩ cache_7, place ⟨78, 2, 1, 3⟩ cache_78] = cache_141 := by
  decide +kernel

theorem load_entry_141 : entryAt 141 = entry_141 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_141 : CacheEquation 141 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(141 < 6)), load_entry_141]
  change forkRow [placeRow ⟨7, 0, 4, 5⟩ (denote cache_7), placeRow ⟨78, 2, 1, 3⟩ (denote cache_78)] = denote cache_141
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_141

theorem verified_row_142 : fork [place ⟨72, 4, 2, 3⟩ cache_72, place ⟨32, 1, 4, 3⟩ cache_32, place ⟨55, 2, 5, 4⟩ cache_55] = cache_142 := by
  decide +kernel

theorem load_entry_142 : entryAt 142 = entry_142 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_142 : CacheEquation 142 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(142 < 6)), load_entry_142]
  change forkRow [placeRow ⟨72, 4, 2, 3⟩ (denote cache_72), placeRow ⟨32, 1, 4, 3⟩ (denote cache_32), placeRow ⟨55, 2, 5, 4⟩ (denote cache_55)] = denote cache_142
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_142

theorem verified_row_143 : fork [place ⟨6, 6, 3, 4⟩ cache_6, place ⟨108, 0, 8, 5⟩ cache_108] = cache_143 := by
  decide +kernel

theorem load_entry_143 : entryAt 143 = entry_143 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_143 : CacheEquation 143 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(143 < 6)), load_entry_143]
  change forkRow [placeRow ⟨6, 6, 3, 4⟩ (denote cache_6), placeRow ⟨108, 0, 8, 5⟩ (denote cache_108)] = denote cache_143
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_143

theorem verified_row_144 : fork [place ⟨7, 0, 4, 5⟩ cache_7, place ⟨104, 4, 1, 5⟩ cache_104, place ⟨55, 0, 5, 4⟩ cache_55] = cache_144 := by
  decide +kernel

theorem load_entry_144 : entryAt 144 = entry_144 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_144 : CacheEquation 144 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(144 < 6)), load_entry_144]
  change forkRow [placeRow ⟨7, 0, 4, 5⟩ (denote cache_7), placeRow ⟨104, 4, 1, 5⟩ (denote cache_104), placeRow ⟨55, 0, 5, 4⟩ (denote cache_55)] = denote cache_144
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_144

theorem verified_row_145 : fork [place ⟨0, 5, 4, 5⟩ cache_0, place ⟨91, 0, 3, 4⟩ cache_91] = cache_145 := by
  decide +kernel

theorem load_entry_145 : entryAt 145 = entry_145 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_145 : CacheEquation 145 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(145 < 6)), load_entry_145]
  change forkRow [placeRow ⟨0, 5, 4, 5⟩ (denote cache_0), placeRow ⟨91, 0, 3, 4⟩ (denote cache_91)] = denote cache_145
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_145

theorem verified_row_146 : fork [place ⟨36, 6, 5, 4⟩ cache_36, place ⟨24, 1, 4, 5⟩ cache_24] = cache_146 := by
  decide +kernel

theorem load_entry_146 : entryAt 146 = entry_146 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_146 : CacheEquation 146 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(146 < 6)), load_entry_146]
  change forkRow [placeRow ⟨36, 6, 5, 4⟩ (denote cache_36), placeRow ⟨24, 1, 4, 5⟩ (denote cache_24)] = denote cache_146
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_146

theorem verified_row_147 : fork [place ⟨53, 0, 1, 5⟩ cache_53, place ⟨44, 2, 5, 4⟩ cache_44] = cache_147 := by
  decide +kernel

theorem load_entry_147 : entryAt 147 = entry_147 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_147 : CacheEquation 147 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(147 < 6)), load_entry_147]
  change forkRow [placeRow ⟨53, 0, 1, 5⟩ (denote cache_53), placeRow ⟨44, 2, 5, 4⟩ (denote cache_44)] = denote cache_147
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_147

theorem verified_row_148 : fork [place ⟨7, 1, 5, 4⟩ cache_7, place ⟨46, 1, 4, 5⟩ cache_46, place ⟨94, 0, 5, 3⟩ cache_94, place ⟨97, 1, 4, 5⟩ cache_97] = cache_148 := by
  decide +kernel

theorem load_entry_148 : entryAt 148 = entry_148 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_148 : CacheEquation 148 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(148 < 6)), load_entry_148]
  change forkRow [placeRow ⟨7, 1, 5, 4⟩ (denote cache_7), placeRow ⟨46, 1, 4, 5⟩ (denote cache_46), placeRow ⟨94, 0, 5, 3⟩ (denote cache_94), placeRow ⟨97, 1, 4, 5⟩ (denote cache_97)] = denote cache_148
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_148

theorem verified_row_149 : fork [place ⟨16, 1, 4, 3⟩ cache_16, place ⟨24, 2, 5, 4⟩ cache_24] = cache_149 := by
  decide +kernel

theorem load_entry_149 : entryAt 149 = entry_149 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_149 : CacheEquation 149 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(149 < 6)), load_entry_149]
  change forkRow [placeRow ⟨16, 1, 4, 3⟩ (denote cache_16), placeRow ⟨24, 2, 5, 4⟩ (denote cache_24)] = denote cache_149
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_149

theorem verified_row_150 : fork [place ⟨4, 6, 1, 3⟩ cache_4, place ⟨126, 5, 2, 5⟩ cache_126] = cache_150 := by
  decide +kernel

theorem load_entry_150 : entryAt 150 = entry_150 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_150 : CacheEquation 150 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(150 < 6)), load_entry_150]
  change forkRow [placeRow ⟨4, 6, 1, 3⟩ (denote cache_4), placeRow ⟨126, 5, 2, 5⟩ (denote cache_126)] = denote cache_150
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_150

theorem verified_row_151 : fork [place ⟨2, 1, 4, 3⟩ cache_2, place ⟨101, 2, 6, 3⟩ cache_101] = cache_151 := by
  decide +kernel

theorem load_entry_151 : entryAt 151 = entry_151 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_151 : CacheEquation 151 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(151 < 6)), load_entry_151]
  change forkRow [placeRow ⟨2, 1, 4, 3⟩ (denote cache_2), placeRow ⟨101, 2, 6, 3⟩ (denote cache_101)] = denote cache_151
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_151

theorem verified_row_152 : fork [place ⟨6, 3, 4, 5⟩ cache_6, place ⟨73, 1, 7, 4⟩ cache_73] = cache_152 := by
  decide +kernel

theorem load_entry_152 : entryAt 152 = entry_152 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_152 : CacheEquation 152 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(152 < 6)), load_entry_152]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (denote cache_6), placeRow ⟨73, 1, 7, 4⟩ (denote cache_73)] = denote cache_152
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_152

theorem verified_row_153 : fork [place ⟨59, 4, 0, 4⟩ cache_59, place ⟨27, 0, 5, 4⟩ cache_27] = cache_153 := by
  decide +kernel

theorem load_entry_153 : entryAt 153 = entry_153 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_153 : CacheEquation 153 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(153 < 6)), load_entry_153]
  change forkRow [placeRow ⟨59, 4, 0, 4⟩ (denote cache_59), placeRow ⟨27, 0, 5, 4⟩ (denote cache_27)] = denote cache_153
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_153

theorem verified_row_154 : fork [place ⟨7, 6, 4, 3⟩ cache_7, place ⟨104, 0, 7, 5⟩ cache_104] = cache_154 := by
  decide +kernel

theorem load_entry_154 : entryAt 154 = entry_154 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_154 : CacheEquation 154 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(154 < 6)), load_entry_154]
  change forkRow [placeRow ⟨7, 6, 4, 3⟩ (denote cache_7), placeRow ⟨104, 0, 7, 5⟩ (denote cache_104)] = denote cache_154
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_154

theorem verified_row_155 : fork [place ⟨7, 1, 5, 4⟩ cache_7, place ⟨55, 3, 4, 5⟩ cache_55] = cache_155 := by
  decide +kernel

theorem load_entry_155 : entryAt 155 = entry_155 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_155 : CacheEquation 155 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(155 < 6)), load_entry_155]
  change forkRow [placeRow ⟨7, 1, 5, 4⟩ (denote cache_7), placeRow ⟨55, 3, 4, 5⟩ (denote cache_55)] = denote cache_155
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_155

theorem verified_row_156 : fork [place ⟨11, 0, 2, 4⟩ cache_11, place ⟨98, 2, 2, 4⟩ cache_98, place ⟨33, 0, 2, 3⟩ cache_33] = cache_156 := by
  decide +kernel

theorem load_entry_156 : entryAt 156 = entry_156 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_156 : CacheEquation 156 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(156 < 6)), load_entry_156]
  change forkRow [placeRow ⟨11, 0, 2, 4⟩ (denote cache_11), placeRow ⟨98, 2, 2, 4⟩ (denote cache_98), placeRow ⟨33, 0, 2, 3⟩ (denote cache_33)] = denote cache_156
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_156

theorem verified_row_157 : fork [place ⟨6, 3, 4, 5⟩ cache_6, place ⟨57, 1, 5, 6⟩ cache_57] = cache_157 := by
  decide +kernel

theorem load_entry_157 : entryAt 157 = entry_157 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_157 : CacheEquation 157 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(157 < 6)), load_entry_157]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (denote cache_6), placeRow ⟨57, 1, 5, 6⟩ (denote cache_57)] = denote cache_157
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_157

theorem verified_row_158 : fork [place ⟨66, 0, 3, 4⟩ cache_66, place ⟨45, 1, 4, 5⟩ cache_45, place ⟨46, 3, 4, 5⟩ cache_46] = cache_158 := by
  decide +kernel

theorem load_entry_158 : entryAt 158 = entry_158 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_158 : CacheEquation 158 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(158 < 6)), load_entry_158]
  change forkRow [placeRow ⟨66, 0, 3, 4⟩ (denote cache_66), placeRow ⟨45, 1, 4, 5⟩ (denote cache_45), placeRow ⟨46, 3, 4, 5⟩ (denote cache_46)] = denote cache_158
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_158

theorem verified_row_159 : fork [place ⟨45, 3, 4, 5⟩ cache_45, place ⟨65, 1, 4, 5⟩ cache_65, place ⟨7, 3, 3, 4⟩ cache_7] = cache_159 := by
  decide +kernel

theorem load_entry_159 : entryAt 159 = entry_159 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_159 : CacheEquation 159 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(159 < 6)), load_entry_159]
  change forkRow [placeRow ⟨45, 3, 4, 5⟩ (denote cache_45), placeRow ⟨65, 1, 4, 5⟩ (denote cache_65), placeRow ⟨7, 3, 3, 4⟩ (denote cache_7)] = denote cache_159
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_159

end SnakyCertificate.Check

end OAI
