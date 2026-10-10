import OAI.Combinatorics.SnakyCertificate.Cache
import OAI.Combinatorics.SnakyCertificate.TableList

namespace OAI

namespace SnakyCertificate.Check

theorem verified_row_80 : fork [place ⟨0, 6, 6, 4⟩ cache_0, place ⟨13, 4, 2, 4⟩ cache_13] = cache_80 := by
  decide +kernel

theorem load_entry_80 : entryAt 80 = entry_80 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_80 : CacheEquation 80 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(80 < 6)), load_entry_80]
  change forkRow [placeRow ⟨0, 6, 6, 4⟩ (denote cache_0), placeRow ⟨13, 4, 2, 4⟩ (denote cache_13)] = denote cache_80
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_80

theorem verified_row_81 : fork [place ⟨4, 3, 4, 3⟩ cache_4, place ⟨43, 0, 5, 4⟩ cache_43] = cache_81 := by
  decide +kernel

theorem load_entry_81 : entryAt 81 = entry_81 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_81 : CacheEquation 81 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(81 < 6)), load_entry_81]
  change forkRow [placeRow ⟨4, 3, 4, 3⟩ (denote cache_4), placeRow ⟨43, 0, 5, 4⟩ (denote cache_43)] = denote cache_81
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_81

theorem verified_row_82 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨36, 0, 1, 3⟩ cache_36] = cache_82 := by
  decide +kernel

theorem load_entry_82 : entryAt 82 = entry_82 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_82 : CacheEquation 82 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(82 < 6)), load_entry_82]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨36, 0, 1, 3⟩ (denote cache_36)] = denote cache_82
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_82

theorem verified_row_83 : fork [place ⟨0, 7, 5, 7⟩ cache_0, place ⟨67, 2, 6, 3⟩ cache_67] = cache_83 := by
  decide +kernel

theorem load_entry_83 : entryAt 83 = entry_83 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_83 : CacheEquation 83 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(83 < 6)), load_entry_83]
  change forkRow [placeRow ⟨0, 7, 5, 7⟩ (denote cache_0), placeRow ⟨67, 2, 6, 3⟩ (denote cache_67)] = denote cache_83
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_83

theorem verified_row_84 : fork [place ⟨6, 3, 4, 5⟩ cache_6, place ⟨67, 0, 6, 4⟩ cache_67] = cache_84 := by
  decide +kernel

theorem load_entry_84 : entryAt 84 = entry_84 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_84 : CacheEquation 84 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(84 < 6)), load_entry_84]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (denote cache_6), placeRow ⟨67, 0, 6, 4⟩ (denote cache_67)] = denote cache_84
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_84

theorem verified_row_85 : fork [place ⟨9, 0, 6, 3⟩ cache_9, place ⟨8, 4, 5, 4⟩ cache_8] = cache_85 := by
  decide +kernel

theorem load_entry_85 : entryAt 85 = entry_85 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_85 : CacheEquation 85 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(85 < 6)), load_entry_85]
  change forkRow [placeRow ⟨9, 0, 6, 3⟩ (denote cache_9), placeRow ⟨8, 4, 5, 4⟩ (denote cache_8)] = denote cache_85
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_85

theorem verified_row_86 : fork [place ⟨0, 6, 5, 4⟩ cache_0, place ⟨67, 3, 1, 5⟩ cache_67] = cache_86 := by
  decide +kernel

theorem load_entry_86 : entryAt 86 = entry_86 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_86 : CacheEquation 86 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(86 < 6)), load_entry_86]
  change forkRow [placeRow ⟨0, 6, 5, 4⟩ (denote cache_0), placeRow ⟨67, 3, 1, 5⟩ (denote cache_67)] = denote cache_86
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_86

theorem verified_row_87 : fork [place ⟨0, 5, 3, 7⟩ cache_0, place ⟨24, 2, 5, 3⟩ cache_24] = cache_87 := by
  decide +kernel

theorem load_entry_87 : entryAt 87 = entry_87 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_87 : CacheEquation 87 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(87 < 6)), load_entry_87]
  change forkRow [placeRow ⟨0, 5, 3, 7⟩ (denote cache_0), placeRow ⟨24, 2, 5, 3⟩ (denote cache_24)] = denote cache_87
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_87

theorem verified_row_88 : fork [place ⟨0, 6, 6, 4⟩ cache_0, place ⟨67, 3, 2, 5⟩ cache_67] = cache_88 := by
  decide +kernel

theorem load_entry_88 : entryAt 88 = entry_88 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_88 : CacheEquation 88 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(88 < 6)), load_entry_88]
  change forkRow [placeRow ⟨0, 6, 6, 4⟩ (denote cache_0), placeRow ⟨67, 3, 2, 5⟩ (denote cache_67)] = denote cache_88
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_88

theorem verified_row_89 : fork [place ⟨8, 3, 3, 1⟩ cache_8, place ⟨7, 1, 5, 4⟩ cache_7] = cache_89 := by
  decide +kernel

theorem load_entry_89 : entryAt 89 = entry_89 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_89 : CacheEquation 89 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(89 < 6)), load_entry_89]
  change forkRow [placeRow ⟨8, 3, 3, 1⟩ (denote cache_8), placeRow ⟨7, 1, 5, 4⟩ (denote cache_7)] = denote cache_89
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_89

theorem verified_row_90 : fork [place ⟨31, 0, 3, 3⟩ cache_31, place ⟨54, 6, 0, 3⟩ cache_54, place ⟨54, 0, 5, 4⟩ cache_54, place ⟨31, 6, 2, 4⟩ cache_31] = cache_90 := by
  decide +kernel

theorem load_entry_90 : entryAt 90 = entry_90 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_90 : CacheEquation 90 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(90 < 6)), load_entry_90]
  change forkRow [placeRow ⟨31, 0, 3, 3⟩ (denote cache_31), placeRow ⟨54, 6, 0, 3⟩ (denote cache_54), placeRow ⟨54, 0, 5, 4⟩ (denote cache_54), placeRow ⟨31, 6, 2, 4⟩ (denote cache_31)] = denote cache_90
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_90

theorem verified_row_91 : fork [place ⟨6, 3, 4, 5⟩ cache_6, place ⟨74, 5, 7, 3⟩ cache_74] = cache_91 := by
  decide +kernel

theorem load_entry_91 : entryAt 91 = entry_91 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_91 : CacheEquation 91 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(91 < 6)), load_entry_91]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (denote cache_6), placeRow ⟨74, 5, 7, 3⟩ (denote cache_74)] = denote cache_91
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_91

theorem verified_row_92 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨33, 0, 2, 3⟩ cache_33] = cache_92 := by
  decide +kernel

theorem load_entry_92 : entryAt 92 = entry_92 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_92 : CacheEquation 92 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(92 < 6)), load_entry_92]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨33, 0, 2, 3⟩ (denote cache_33)] = denote cache_92
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_92

theorem verified_row_93 : fork [place ⟨4, 3, 4, 3⟩ cache_4, place ⟨47, 0, 5, 4⟩ cache_47] = cache_93 := by
  decide +kernel

theorem load_entry_93 : entryAt 93 = entry_93 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_93 : CacheEquation 93 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(93 < 6)), load_entry_93]
  change forkRow [placeRow ⟨4, 3, 4, 3⟩ (denote cache_4), placeRow ⟨47, 0, 5, 4⟩ (denote cache_47)] = denote cache_93
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_93

theorem verified_row_94 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨27, 3, 3, 6⟩ cache_27] = cache_94 := by
  decide +kernel

theorem load_entry_94 : entryAt 94 = entry_94 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_94 : CacheEquation 94 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(94 < 6)), load_entry_94]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨27, 3, 3, 6⟩ (denote cache_27)] = denote cache_94
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_94

theorem verified_row_95 : fork [place ⟨0, 5, 3, 7⟩ cache_0, place ⟨29, 0, 2, 5⟩ cache_29] = cache_95 := by
  decide +kernel

theorem load_entry_95 : entryAt 95 = entry_95 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_95 : CacheEquation 95 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(95 < 6)), load_entry_95]
  change forkRow [placeRow ⟨0, 5, 3, 7⟩ (denote cache_0), placeRow ⟨29, 0, 2, 5⟩ (denote cache_29)] = denote cache_95
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_95

theorem verified_row_96 : fork [place ⟨6, 1, 5, 5⟩ cache_6, place ⟨70, 0, 3, 5⟩ cache_70] = cache_96 := by
  decide +kernel

theorem load_entry_96 : entryAt 96 = entry_96 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_96 : CacheEquation 96 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(96 < 6)), load_entry_96]
  change forkRow [placeRow ⟨6, 1, 5, 5⟩ (denote cache_6), placeRow ⟨70, 0, 3, 5⟩ (denote cache_70)] = denote cache_96
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_96

theorem verified_row_97 : fork [place ⟨6, 6, 0, 3⟩ cache_6, place ⟨44, 0, 5, 4⟩ cache_44] = cache_97 := by
  decide +kernel

theorem load_entry_97 : entryAt 97 = entry_97 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_97 : CacheEquation 97 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(97 < 6)), load_entry_97]
  change forkRow [placeRow ⟨6, 6, 0, 3⟩ (denote cache_6), placeRow ⟨44, 0, 5, 4⟩ (denote cache_44)] = denote cache_97
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_97

theorem verified_row_98 : fork [place ⟨6, 6, 2, 3⟩ cache_6, place ⟨44, 0, 7, 4⟩ cache_44] = cache_98 := by
  decide +kernel

theorem load_entry_98 : entryAt 98 = entry_98 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_98 : CacheEquation 98 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(98 < 6)), load_entry_98]
  change forkRow [placeRow ⟨6, 6, 2, 3⟩ (denote cache_6), placeRow ⟨44, 0, 7, 4⟩ (denote cache_44)] = denote cache_98
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_98

theorem verified_row_99 : fork [place ⟨2, 1, 3, 2⟩ cache_2, place ⟨24, 0, 5, 4⟩ cache_24] = cache_99 := by
  decide +kernel

theorem load_entry_99 : entryAt 99 = entry_99 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_99 : CacheEquation 99 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(99 < 6)), load_entry_99]
  change forkRow [placeRow ⟨2, 1, 3, 2⟩ (denote cache_2), placeRow ⟨24, 0, 5, 4⟩ (denote cache_24)] = denote cache_99
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_99

theorem verified_row_100 : fork [place ⟨0, 6, 5, 4⟩ cache_0, place ⟨48, 0, 1, 4⟩ cache_48] = cache_100 := by
  decide +kernel

theorem load_entry_100 : entryAt 100 = entry_100 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_100 : CacheEquation 100 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(100 < 6)), load_entry_100]
  change forkRow [placeRow ⟨0, 6, 5, 4⟩ (denote cache_0), placeRow ⟨48, 0, 1, 4⟩ (denote cache_48)] = denote cache_100
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_100

theorem verified_row_101 : fork [place ⟨0, 7, 4, 6⟩ cache_0, place ⟨24, 0, 5, 4⟩ cache_24] = cache_101 := by
  decide +kernel

theorem load_entry_101 : entryAt 101 = entry_101 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_101 : CacheEquation 101 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(101 < 6)), load_entry_101]
  change forkRow [placeRow ⟨0, 7, 4, 6⟩ (denote cache_0), placeRow ⟨24, 0, 5, 4⟩ (denote cache_24)] = denote cache_101
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_101

theorem verified_row_102 : fork [place ⟨6, 3, 4, 5⟩ cache_6, place ⟨25, 2, 6, 3⟩ cache_25] = cache_102 := by
  decide +kernel

theorem load_entry_102 : entryAt 102 = entry_102 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_102 : CacheEquation 102 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(102 < 6)), load_entry_102]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (denote cache_6), placeRow ⟨25, 2, 6, 3⟩ (denote cache_25)] = denote cache_102
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_102

theorem verified_row_103 : fork [place ⟨6, 3, 4, 5⟩ cache_6, place ⟨71, 0, 6, 4⟩ cache_71] = cache_103 := by
  decide +kernel

theorem load_entry_103 : entryAt 103 = entry_103 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_103 : CacheEquation 103 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(103 < 6)), load_entry_103]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (denote cache_6), placeRow ⟨71, 0, 6, 4⟩ (denote cache_71)] = denote cache_103
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_103

theorem verified_row_104 : fork [place ⟨6, 0, 5, 4⟩ cache_6, place ⟨75, 0, 3, 4⟩ cache_75] = cache_104 := by
  decide +kernel

theorem load_entry_104 : entryAt 104 = entry_104 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_104 : CacheEquation 104 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(104 < 6)), load_entry_104]
  change forkRow [placeRow ⟨6, 0, 5, 4⟩ (denote cache_6), placeRow ⟨75, 0, 3, 4⟩ (denote cache_75)] = denote cache_104
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_104

theorem verified_row_105 : fork [place ⟨6, 5, 4, 3⟩ cache_6, place ⟨77, 0, 4, 5⟩ cache_77] = cache_105 := by
  decide +kernel

theorem load_entry_105 : entryAt 105 = entry_105 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_105 : CacheEquation 105 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(105 < 6)), load_entry_105]
  change forkRow [placeRow ⟨6, 5, 4, 3⟩ (denote cache_6), placeRow ⟨77, 0, 4, 5⟩ (denote cache_77)] = denote cache_105
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_105

theorem verified_row_106 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨36, 6, 5, 4⟩ cache_36] = cache_106 := by
  decide +kernel

theorem load_entry_106 : entryAt 106 = entry_106 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_106 : CacheEquation 106 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(106 < 6)), load_entry_106]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨36, 6, 5, 4⟩ (denote cache_36)] = denote cache_106
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_106

theorem verified_row_107 : fork [place ⟨6, 6, 0, 3⟩ cache_6, place ⟨63, 1, 5, 3⟩ cache_63] = cache_107 := by
  decide +kernel

theorem load_entry_107 : entryAt 107 = entry_107 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_107 : CacheEquation 107 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(107 < 6)), load_entry_107]
  change forkRow [placeRow ⟨6, 6, 0, 3⟩ (denote cache_6), placeRow ⟨63, 1, 5, 3⟩ (denote cache_63)] = denote cache_107
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_107

theorem verified_row_108 : fork [place ⟨4, 6, 1, 3⟩ cache_4, place ⟨63, 1, 5, 3⟩ cache_63] = cache_108 := by
  decide +kernel

theorem load_entry_108 : entryAt 108 = entry_108 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_108 : CacheEquation 108 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(108 < 6)), load_entry_108]
  change forkRow [placeRow ⟨4, 6, 1, 3⟩ (denote cache_4), placeRow ⟨63, 1, 5, 3⟩ (denote cache_63)] = denote cache_108
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_108

theorem verified_row_109 : fork [place ⟨4, 6, 1, 3⟩ cache_4, place ⟨55, 0, 5, 4⟩ cache_55] = cache_109 := by
  decide +kernel

theorem load_entry_109 : entryAt 109 = entry_109 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_109 : CacheEquation 109 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(109 < 6)), load_entry_109]
  change forkRow [placeRow ⟨4, 6, 1, 3⟩ (denote cache_4), placeRow ⟨55, 0, 5, 4⟩ (denote cache_55)] = denote cache_109
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_109

theorem verified_row_110 : fork [place ⟨6, 6, 1, 3⟩ cache_6, place ⟨63, 1, 6, 3⟩ cache_63] = cache_110 := by
  decide +kernel

theorem load_entry_110 : entryAt 110 = entry_110 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_110 : CacheEquation 110 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(110 < 6)), load_entry_110]
  change forkRow [placeRow ⟨6, 6, 1, 3⟩ (denote cache_6), placeRow ⟨63, 1, 6, 3⟩ (denote cache_63)] = denote cache_110
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_110

theorem verified_row_111 : fork [place ⟨6, 7, 4, 3⟩ cache_6, place ⟨83, 0, 4, 5⟩ cache_83] = cache_111 := by
  decide +kernel

theorem load_entry_111 : entryAt 111 = entry_111 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_111 : CacheEquation 111 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(111 < 6)), load_entry_111]
  change forkRow [placeRow ⟨6, 7, 4, 3⟩ (denote cache_6), placeRow ⟨83, 0, 4, 5⟩ (denote cache_83)] = denote cache_111
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_111

theorem verified_row_112 : fork [place ⟨4, 1, 5, 4⟩ cache_4, place ⟨93, 0, 3, 5⟩ cache_93] = cache_112 := by
  decide +kernel

theorem load_entry_112 : entryAt 112 = entry_112 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_112 : CacheEquation 112 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(112 < 6)), load_entry_112]
  change forkRow [placeRow ⟨4, 1, 5, 4⟩ (denote cache_4), placeRow ⟨93, 0, 3, 5⟩ (denote cache_93)] = denote cache_112
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_112

theorem verified_row_113 : fork [place ⟨1, 6, 6, 4⟩ cache_1, place ⟨36, 6, 7, 5⟩ cache_36] = cache_113 := by
  decide +kernel

theorem load_entry_113 : entryAt 113 = entry_113 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_113 : CacheEquation 113 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(113 < 6)), load_entry_113]
  change forkRow [placeRow ⟨1, 6, 6, 4⟩ (denote cache_1), placeRow ⟨36, 6, 7, 5⟩ (denote cache_36)] = denote cache_113
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_113

theorem verified_row_114 : fork [place ⟨6, 0, 6, 5⟩ cache_6, place ⟨67, 3, 2, 5⟩ cache_67] = cache_114 := by
  decide +kernel

theorem load_entry_114 : entryAt 114 = entry_114 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_114 : CacheEquation 114 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(114 < 6)), load_entry_114]
  change forkRow [placeRow ⟨6, 0, 6, 5⟩ (denote cache_6), placeRow ⟨67, 3, 2, 5⟩ (denote cache_67)] = denote cache_114
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_114

theorem verified_row_115 : fork [place ⟨6, 2, 7, 3⟩ cache_6, place ⟨70, 7, 2, 5⟩ cache_70] = cache_115 := by
  decide +kernel

theorem load_entry_115 : entryAt 115 = entry_115 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_115 : CacheEquation 115 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(115 < 6)), load_entry_115]
  change forkRow [placeRow ⟨6, 2, 7, 3⟩ (denote cache_6), placeRow ⟨70, 7, 2, 5⟩ (denote cache_70)] = denote cache_115
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_115

theorem verified_row_116 : fork [place ⟨0, 7, 4, 6⟩ cache_0, place ⟨24, 2, 5, 4⟩ cache_24] = cache_116 := by
  decide +kernel

theorem load_entry_116 : entryAt 116 = entry_116 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_116 : CacheEquation 116 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(116 < 6)), load_entry_116]
  change forkRow [placeRow ⟨0, 7, 4, 6⟩ (denote cache_0), placeRow ⟨24, 2, 5, 4⟩ (denote cache_24)] = denote cache_116
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_116

theorem verified_row_117 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨100, 0, 5, 4⟩ cache_100] = cache_117 := by
  decide +kernel

theorem load_entry_117 : entryAt 117 = entry_117 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_117 : CacheEquation 117 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(117 < 6)), load_entry_117]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨100, 0, 5, 4⟩ (denote cache_100)] = denote cache_117
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_117

theorem verified_row_118 : fork [place ⟨4, 7, 3, 1⟩ cache_4, place ⟨61, 1, 5, 4⟩ cache_61] = cache_118 := by
  decide +kernel

theorem load_entry_118 : entryAt 118 = entry_118 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_118 : CacheEquation 118 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(118 < 6)), load_entry_118]
  change forkRow [placeRow ⟨4, 7, 3, 1⟩ (denote cache_4), placeRow ⟨61, 1, 5, 4⟩ (denote cache_61)] = denote cache_118
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_118

theorem verified_row_119 : fork [place ⟨6, 6, 1, 3⟩ cache_6, place ⟨55, 0, 6, 4⟩ cache_55] = cache_119 := by
  decide +kernel

theorem load_entry_119 : entryAt 119 = entry_119 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_119 : CacheEquation 119 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(119 < 6)), load_entry_119]
  change forkRow [placeRow ⟨6, 6, 1, 3⟩ (denote cache_6), placeRow ⟨55, 0, 6, 4⟩ (denote cache_55)] = denote cache_119
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_119

end SnakyCertificate.Check

end OAI
