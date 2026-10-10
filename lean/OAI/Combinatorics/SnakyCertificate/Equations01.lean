import OAI.Combinatorics.SnakyCertificate.Cache
import OAI.Combinatorics.SnakyCertificate.TableList

namespace OAI

namespace SnakyCertificate.Check

theorem verified_row_40 : fork [place ⟨3, 0, 4, 3⟩ cache_3, place ⟨16, 0, 3, 4⟩ cache_16] = cache_40 := by
  decide +kernel

theorem load_entry_40 : entryAt 40 = entry_40 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_40 : CacheEquation 40 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(40 < 6)), load_entry_40]
  change forkRow [placeRow ⟨3, 0, 4, 3⟩ (denote cache_3), placeRow ⟨16, 0, 3, 4⟩ (denote cache_16)] = denote cache_40
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_40

theorem verified_row_41 : fork [place ⟨6, 3, 3, 5⟩ cache_6, place ⟨1, 4, 6, 3⟩ cache_1] = cache_41 := by
  decide +kernel

theorem load_entry_41 : entryAt 41 = entry_41 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_41 : CacheEquation 41 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(41 < 6)), load_entry_41]
  change forkRow [placeRow ⟨6, 3, 3, 5⟩ (denote cache_6), placeRow ⟨1, 4, 6, 3⟩ (denote cache_1)] = denote cache_41
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_41

theorem verified_row_42 : fork [place ⟨0, 6, 6, 4⟩ cache_0, place ⟨6, 4, 1, 5⟩ cache_6] = cache_42 := by
  decide +kernel

theorem load_entry_42 : entryAt 42 = entry_42 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_42 : CacheEquation 42 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(42 < 6)), load_entry_42]
  change forkRow [placeRow ⟨0, 6, 6, 4⟩ (denote cache_0), placeRow ⟨6, 4, 1, 5⟩ (denote cache_6)] = denote cache_42
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_42

theorem verified_row_43 : fork [place ⟨2, 4, 5, 3⟩ cache_2, place ⟨6, 3, 3, 5⟩ cache_6] = cache_43 := by
  decide +kernel

theorem load_entry_43 : entryAt 43 = entry_43 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_43 : CacheEquation 43 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(43 < 6)), load_entry_43]
  change forkRow [placeRow ⟨2, 4, 5, 3⟩ (denote cache_2), placeRow ⟨6, 3, 3, 5⟩ (denote cache_6)] = denote cache_43
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_43

theorem verified_row_44 : fork [place ⟨4, 4, 1, 5⟩ cache_4, place ⟨7, 0, 4, 5⟩ cache_7] = cache_44 := by
  decide +kernel

theorem load_entry_44 : entryAt 44 = entry_44 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_44 : CacheEquation 44 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(44 < 6)), load_entry_44]
  change forkRow [placeRow ⟨4, 4, 1, 5⟩ (denote cache_4), placeRow ⟨7, 0, 4, 5⟩ (denote cache_7)] = denote cache_44
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_44

theorem verified_row_45 : fork [place ⟨6, 4, 0, 5⟩ cache_6, place ⟨7, 0, 4, 5⟩ cache_7] = cache_45 := by
  decide +kernel

theorem load_entry_45 : entryAt 45 = entry_45 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_45 : CacheEquation 45 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(45 < 6)), load_entry_45]
  change forkRow [placeRow ⟨6, 4, 0, 5⟩ (denote cache_6), placeRow ⟨7, 0, 4, 5⟩ (denote cache_7)] = denote cache_45
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_45

theorem verified_row_46 : fork [place ⟨6, 6, 0, 3⟩ cache_6, place ⟨7, 0, 4, 5⟩ cache_7] = cache_46 := by
  decide +kernel

theorem load_entry_46 : entryAt 46 = entry_46 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_46 : CacheEquation 46 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(46 < 6)), load_entry_46]
  change forkRow [placeRow ⟨6, 6, 0, 3⟩ (denote cache_6), placeRow ⟨7, 0, 4, 5⟩ (denote cache_7)] = denote cache_46
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_46

theorem verified_row_47 : fork [place ⟨6, 3, 3, 5⟩ cache_6, place ⟨6, 2, 7, 3⟩ cache_6] = cache_47 := by
  decide +kernel

theorem load_entry_47 : entryAt 47 = entry_47 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_47 : CacheEquation 47 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(47 < 6)), load_entry_47]
  change forkRow [placeRow ⟨6, 3, 3, 5⟩ (denote cache_6), placeRow ⟨6, 2, 7, 3⟩ (denote cache_6)] = denote cache_47
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_47

theorem verified_row_48 : fork [place ⟨6, 3, 4, 5⟩ cache_6, place ⟨6, 2, 8, 3⟩ cache_6] = cache_48 := by
  decide +kernel

theorem load_entry_48 : entryAt 48 = entry_48 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_48 : CacheEquation 48 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(48 < 6)), load_entry_48]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (denote cache_6), placeRow ⟨6, 2, 8, 3⟩ (denote cache_6)] = denote cache_48
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_48

theorem verified_row_49 : fork [place ⟨4, 7, 3, 1⟩ cache_4, place ⟨7, 1, 5, 4⟩ cache_7] = cache_49 := by
  decide +kernel

theorem load_entry_49 : entryAt 49 = entry_49 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_49 : CacheEquation 49 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(49 < 6)), load_entry_49]
  change forkRow [placeRow ⟨4, 7, 3, 1⟩ (denote cache_4), placeRow ⟨7, 1, 5, 4⟩ (denote cache_7)] = denote cache_49
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_49

theorem verified_row_50 : fork [place ⟨6, 3, 3, 5⟩ cache_6, place ⟨7, 1, 5, 4⟩ cache_7] = cache_50 := by
  decide +kernel

theorem load_entry_50 : entryAt 50 = entry_50 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_50 : CacheEquation 50 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(50 < 6)), load_entry_50]
  change forkRow [placeRow ⟨6, 3, 3, 5⟩ (denote cache_6), placeRow ⟨7, 1, 5, 4⟩ (denote cache_7)] = denote cache_50
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_50

theorem verified_row_51 : fork [place ⟨10, 2, 5, 3⟩ cache_10, place ⟨10, 0, 5, 4⟩ cache_10, place ⟨26, 2, 3, 4⟩ cache_26, place ⟨26, 0, 3, 3⟩ cache_26] = cache_51 := by
  decide +kernel

theorem load_entry_51 : entryAt 51 = entry_51 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_51 : CacheEquation 51 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(51 < 6)), load_entry_51]
  change forkRow [placeRow ⟨10, 2, 5, 3⟩ (denote cache_10), placeRow ⟨10, 0, 5, 4⟩ (denote cache_10), placeRow ⟨26, 2, 3, 4⟩ (denote cache_26), placeRow ⟨26, 0, 3, 3⟩ (denote cache_26)] = denote cache_51
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_51

theorem verified_row_52 : fork [place ⟨0, 0, 0, 3⟩ cache_0, place ⟨0, 4, 7, 3⟩ cache_0] = cache_52 := by
  decide +kernel

theorem load_entry_52 : entryAt 52 = entry_52 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_52 : CacheEquation 52 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(52 < 6)), load_entry_52]
  change forkRow [placeRow ⟨0, 0, 0, 3⟩ (denote cache_0), placeRow ⟨0, 4, 7, 3⟩ (denote cache_0)] = denote cache_52
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_52

theorem verified_row_53 : fork [place ⟨6, 4, 3, 4⟩ cache_6, place ⟨3, 1, 4, 5⟩ cache_3] = cache_53 := by
  decide +kernel

theorem load_entry_53 : entryAt 53 = entry_53 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_53 : CacheEquation 53 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(53 < 6)), load_entry_53]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (denote cache_6), placeRow ⟨3, 1, 4, 5⟩ (denote cache_3)] = denote cache_53
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_53

theorem verified_row_54 : fork [place ⟨22, 0, 2, 3⟩ cache_22, place ⟨3, 6, 1, 4⟩ cache_3] = cache_54 := by
  decide +kernel

theorem load_entry_54 : entryAt 54 = entry_54 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_54 : CacheEquation 54 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(54 < 6)), load_entry_54]
  change forkRow [placeRow ⟨22, 0, 2, 3⟩ (denote cache_22), placeRow ⟨3, 6, 1, 4⟩ (denote cache_3)] = denote cache_54
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_54

theorem verified_row_55 : fork [place ⟨7, 4, 0, 5⟩ cache_7, place ⟨7, 0, 4, 5⟩ cache_7] = cache_55 := by
  decide +kernel

theorem load_entry_55 : entryAt 55 = entry_55 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_55 : CacheEquation 55 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(55 < 6)), load_entry_55]
  change forkRow [placeRow ⟨7, 4, 0, 5⟩ (denote cache_7), placeRow ⟨7, 0, 4, 5⟩ (denote cache_7)] = denote cache_55
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_55

theorem verified_row_56 : fork [place ⟨7, 4, 0, 5⟩ cache_7, place ⟨7, 6, 0, 3⟩ cache_7] = cache_56 := by
  decide +kernel

theorem load_entry_56 : entryAt 56 = entry_56 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_56 : CacheEquation 56 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(56 < 6)), load_entry_56]
  change forkRow [placeRow ⟨7, 4, 0, 5⟩ (denote cache_7), placeRow ⟨7, 6, 0, 3⟩ (denote cache_7)] = denote cache_56
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_56

theorem verified_row_57 : fork [place ⟨0, 6, 5, 4⟩ cache_0, place ⟨7, 0, 4, 5⟩ cache_7] = cache_57 := by
  decide +kernel

theorem load_entry_57 : entryAt 57 = entry_57 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_57 : CacheEquation 57 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(57 < 6)), load_entry_57]
  change forkRow [placeRow ⟨0, 6, 5, 4⟩ (denote cache_0), placeRow ⟨7, 0, 4, 5⟩ (denote cache_7)] = denote cache_57
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_57

theorem verified_row_58 : fork [place ⟨0, 4, 5, 4⟩ cache_0, place ⟨7, 0, 4, 5⟩ cache_7] = cache_58 := by
  decide +kernel

theorem load_entry_58 : entryAt 58 = entry_58 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_58 : CacheEquation 58 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(58 < 6)), load_entry_58]
  change forkRow [placeRow ⟨0, 4, 5, 4⟩ (denote cache_0), placeRow ⟨7, 0, 4, 5⟩ (denote cache_7)] = denote cache_58
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_58

theorem verified_row_59 : fork [place ⟨0, 6, 5, 4⟩ cache_0, place ⟨7, 4, 0, 5⟩ cache_7] = cache_59 := by
  decide +kernel

theorem load_entry_59 : entryAt 59 = entry_59 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_59 : CacheEquation 59 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(59 < 6)), load_entry_59]
  change forkRow [placeRow ⟨0, 6, 5, 4⟩ (denote cache_0), placeRow ⟨7, 4, 0, 5⟩ (denote cache_7)] = denote cache_59
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_59

theorem verified_row_60 : fork [place ⟨6, 6, 1, 3⟩ cache_6, place ⟨49, 1, 6, 4⟩ cache_49] = cache_60 := by
  decide +kernel

theorem load_entry_60 : entryAt 60 = entry_60 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_60 : CacheEquation 60 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(60 < 6)), load_entry_60]
  change forkRow [placeRow ⟨6, 6, 1, 3⟩ (denote cache_6), placeRow ⟨49, 1, 6, 4⟩ (denote cache_49)] = denote cache_60
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_60

theorem verified_row_61 : fork [place ⟨6, 0, 5, 4⟩ cache_6, place ⟨14, 1, 4, 5⟩ cache_14] = cache_61 := by
  decide +kernel

theorem load_entry_61 : entryAt 61 = entry_61 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_61 : CacheEquation 61 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(61 < 6)), load_entry_61]
  change forkRow [placeRow ⟨6, 0, 5, 4⟩ (denote cache_6), placeRow ⟨14, 1, 4, 5⟩ (denote cache_14)] = denote cache_61
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_61

theorem verified_row_62 : fork [place ⟨6, 6, 0, 3⟩ cache_6, place ⟨53, 0, 1, 5⟩ cache_53] = cache_62 := by
  decide +kernel

theorem load_entry_62 : entryAt 62 = entry_62 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_62 : CacheEquation 62 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(62 < 6)), load_entry_62]
  change forkRow [placeRow ⟨6, 6, 0, 3⟩ (denote cache_6), placeRow ⟨53, 0, 1, 5⟩ (denote cache_53)] = denote cache_62
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_62

theorem verified_row_63 : fork [place ⟨4, 3, 4, 3⟩ cache_4, place ⟨50, 0, 5, 4⟩ cache_50] = cache_63 := by
  decide +kernel

theorem load_entry_63 : entryAt 63 = entry_63 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_63 : CacheEquation 63 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(63 < 6)), load_entry_63]
  change forkRow [placeRow ⟨4, 3, 4, 3⟩ (denote cache_4), placeRow ⟨50, 0, 5, 4⟩ (denote cache_50)] = denote cache_63
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_63

theorem verified_row_64 : fork [place ⟨6, 6, 3, 4⟩ cache_6, place ⟨49, 1, 8, 5⟩ cache_49] = cache_64 := by
  decide +kernel

theorem load_entry_64 : entryAt 64 = entry_64 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_64 : CacheEquation 64 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(64 < 6)), load_entry_64]
  change forkRow [placeRow ⟨6, 6, 3, 4⟩ (denote cache_6), placeRow ⟨49, 1, 8, 5⟩ (denote cache_49)] = denote cache_64
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_64

theorem verified_row_65 : fork [place ⟨6, 6, 0, 3⟩ cache_6, place ⟨49, 1, 5, 4⟩ cache_49] = cache_65 := by
  decide +kernel

theorem load_entry_65 : entryAt 65 = entry_65 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_65 : CacheEquation 65 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(65 < 6)), load_entry_65]
  change forkRow [placeRow ⟨6, 6, 0, 3⟩ (denote cache_6), placeRow ⟨49, 1, 5, 4⟩ (denote cache_49)] = denote cache_65
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_65

theorem verified_row_66 : fork [place ⟨6, 3, 4, 5⟩ cache_6, place ⟨53, 5, 6, 4⟩ cache_53] = cache_66 := by
  decide +kernel

theorem load_entry_66 : entryAt 66 = entry_66 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_66 : CacheEquation 66 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(66 < 6)), load_entry_66]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (denote cache_6), placeRow ⟨53, 5, 6, 4⟩ (denote cache_53)] = denote cache_66
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_66

theorem verified_row_67 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨9, 2, 5, 4⟩ cache_9] = cache_67 := by
  decide +kernel

theorem load_entry_67 : entryAt 67 = entry_67 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_67 : CacheEquation 67 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(67 < 6)), load_entry_67]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨9, 2, 5, 4⟩ (denote cache_9)] = denote cache_67
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_67

theorem verified_row_68 : fork [place ⟨6, 4, 0, 5⟩ cache_6, place ⟨44, 0, 5, 4⟩ cache_44] = cache_68 := by
  decide +kernel

theorem load_entry_68 : entryAt 68 = entry_68 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_68 : CacheEquation 68 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(68 < 6)), load_entry_68]
  change forkRow [placeRow ⟨6, 4, 0, 5⟩ (denote cache_6), placeRow ⟨44, 0, 5, 4⟩ (denote cache_44)] = denote cache_68
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_68

theorem verified_row_69 : fork [place ⟨6, 3, 4, 5⟩ cache_6, place ⟨34, 0, 6, 5⟩ cache_34] = cache_69 := by
  decide +kernel

theorem load_entry_69 : entryAt 69 = entry_69 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_69 : CacheEquation 69 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(69 < 6)), load_entry_69]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (denote cache_6), placeRow ⟨34, 0, 6, 5⟩ (denote cache_34)] = denote cache_69
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_69

theorem verified_row_70 : fork [place ⟨4, 3, 4, 3⟩ cache_4, place ⟨41, 0, 5, 4⟩ cache_41] = cache_70 := by
  decide +kernel

theorem load_entry_70 : entryAt 70 = entry_70 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_70 : CacheEquation 70 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(70 < 6)), load_entry_70]
  change forkRow [placeRow ⟨4, 3, 4, 3⟩ (denote cache_4), placeRow ⟨41, 0, 5, 4⟩ (denote cache_41)] = denote cache_70
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_70

theorem verified_row_71 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨23, 2, 4, 3⟩ cache_23] = cache_71 := by
  decide +kernel

theorem load_entry_71 : entryAt 71 = entry_71 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_71 : CacheEquation 71 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(71 < 6)), load_entry_71]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨23, 2, 4, 3⟩ (denote cache_23)] = denote cache_71
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_71

theorem verified_row_72 : fork [place ⟨0, 5, 3, 8⟩ cache_0, place ⟨8, 6, 5, 4⟩ cache_8] = cache_72 := by
  decide +kernel

theorem load_entry_72 : entryAt 72 = entry_72 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_72 : CacheEquation 72 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(72 < 6)), load_entry_72]
  change forkRow [placeRow ⟨0, 5, 3, 8⟩ (denote cache_0), placeRow ⟨8, 6, 5, 4⟩ (denote cache_8)] = denote cache_72
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_72

theorem verified_row_73 : fork [place ⟨4, 3, 3, 4⟩ cache_4, place ⟨50, 0, 4, 5⟩ cache_50] = cache_73 := by
  decide +kernel

theorem load_entry_73 : entryAt 73 = entry_73 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_73 : CacheEquation 73 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(73 < 6)), load_entry_73]
  change forkRow [placeRow ⟨4, 3, 3, 4⟩ (denote cache_4), placeRow ⟨50, 0, 4, 5⟩ (denote cache_50)] = denote cache_73
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_73

theorem verified_row_74 : fork [place ⟨2, 7, 4, 3⟩ cache_2, place ⟨53, 0, 3, 3⟩ cache_53] = cache_74 := by
  decide +kernel

theorem load_entry_74 : entryAt 74 = entry_74 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_74 : CacheEquation 74 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(74 < 6)), load_entry_74]
  change forkRow [placeRow ⟨2, 7, 4, 3⟩ (denote cache_2), placeRow ⟨53, 0, 3, 3⟩ (denote cache_53)] = denote cache_74
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_74

theorem verified_row_75 : fork [place ⟨0, 0, 1, 3⟩ cache_0, place ⟨9, 0, 7, 3⟩ cache_9] = cache_75 := by
  decide +kernel

theorem load_entry_75 : entryAt 75 = entry_75 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_75 : CacheEquation 75 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(75 < 6)), load_entry_75]
  change forkRow [placeRow ⟨0, 0, 1, 3⟩ (denote cache_0), placeRow ⟨9, 0, 7, 3⟩ (denote cache_9)] = denote cache_75
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_75

theorem verified_row_76 : fork [place ⟨0, 7, 5, 7⟩ cache_0, place ⟨14, 0, 7, 5⟩ cache_14] = cache_76 := by
  decide +kernel

theorem load_entry_76 : entryAt 76 = entry_76 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_76 : CacheEquation 76 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(76 < 6)), load_entry_76]
  change forkRow [placeRow ⟨0, 7, 5, 7⟩ (denote cache_0), placeRow ⟨14, 0, 7, 5⟩ (denote cache_14)] = denote cache_76
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_76

theorem verified_row_77 : fork [place ⟨0, 5, 3, 7⟩ cache_0, place ⟨12, 0, 5, 4⟩ cache_12] = cache_77 := by
  decide +kernel

theorem load_entry_77 : entryAt 77 = entry_77 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_77 : CacheEquation 77 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(77 < 6)), load_entry_77]
  change forkRow [placeRow ⟨0, 5, 3, 7⟩ (denote cache_0), placeRow ⟨12, 0, 5, 4⟩ (denote cache_12)] = denote cache_77
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_77

theorem verified_row_78 : fork [place ⟨6, 4, 3, 4⟩ cache_6, place ⟨52, 0, 5, 4⟩ cache_52] = cache_78 := by
  decide +kernel

theorem load_entry_78 : entryAt 78 = entry_78 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_78 : CacheEquation 78 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(78 < 6)), load_entry_78]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (denote cache_6), placeRow ⟨52, 0, 5, 4⟩ (denote cache_52)] = denote cache_78
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_78

theorem verified_row_79 : fork [place ⟨6, 1, 5, 5⟩ cache_6, place ⟨48, 0, 3, 4⟩ cache_48] = cache_79 := by
  decide +kernel

theorem load_entry_79 : entryAt 79 = entry_79 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_79 : CacheEquation 79 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(79 < 6)), load_entry_79]
  change forkRow [placeRow ⟨6, 1, 5, 5⟩ (denote cache_6), placeRow ⟨48, 0, 3, 4⟩ (denote cache_48)] = denote cache_79
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_79

end SnakyCertificate.Check

end OAI
