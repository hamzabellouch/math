import OAI.Combinatorics.SnakyCertificate.Cache
import OAI.Combinatorics.SnakyCertificate.TableList

namespace OAI

namespace SnakyCertificate.Check

theorem cache_equation_0 : CacheEquation 0 := by
  unfold CacheEquation
  decide +kernel

theorem cache_equation_1 : CacheEquation 1 := by
  unfold CacheEquation
  decide +kernel

theorem cache_equation_2 : CacheEquation 2 := by
  unfold CacheEquation
  decide +kernel

theorem cache_equation_3 : CacheEquation 3 := by
  unfold CacheEquation
  decide +kernel

theorem cache_equation_4 : CacheEquation 4 := by
  unfold CacheEquation
  decide +kernel

theorem cache_equation_5 : CacheEquation 5 := by
  unfold CacheEquation
  decide +kernel

theorem verified_row_6 : fork [place ⟨0, 0, 0, 3⟩ cache_0] = cache_6 := by
  decide +kernel

theorem load_entry_6 : entryAt 6 = entry_6 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_6 : CacheEquation 6 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(6 < 6)), load_entry_6]
  change forkRow [placeRow ⟨0, 0, 0, 3⟩ (denote cache_0)] = denote cache_6
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_6

theorem verified_row_7 : fork [place ⟨4, 0, 3, 4⟩ cache_4, place ⟨6, 0, 5, 4⟩ cache_6] = cache_7 := by
  decide +kernel

theorem load_entry_7 : entryAt 7 = entry_7 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_7 : CacheEquation 7 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(7 < 6)), load_entry_7]
  change forkRow [placeRow ⟨4, 0, 3, 4⟩ (denote cache_4), placeRow ⟨6, 0, 5, 4⟩ (denote cache_6)] = denote cache_7
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_7

theorem verified_row_8 : fork [place ⟨0, 4, 8, 3⟩ cache_0, place ⟨6, 4, 3, 4⟩ cache_6] = cache_8 := by
  decide +kernel

theorem load_entry_8 : entryAt 8 = entry_8 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_8 : CacheEquation 8 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(8 < 6)), load_entry_8]
  change forkRow [placeRow ⟨0, 4, 8, 3⟩ (denote cache_0), placeRow ⟨6, 4, 3, 4⟩ (denote cache_6)] = denote cache_8
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_8

theorem verified_row_9 : fork [place ⟨0, 4, 5, 4⟩ cache_0, place ⟨6, 4, 0, 5⟩ cache_6] = cache_9 := by
  decide +kernel

theorem load_entry_9 : entryAt 9 = entry_9 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_9 : CacheEquation 9 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(9 < 6)), load_entry_9]
  change forkRow [placeRow ⟨0, 4, 5, 4⟩ (denote cache_0), placeRow ⟨6, 4, 0, 5⟩ (denote cache_6)] = denote cache_9
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_9

theorem verified_row_10 : fork [place ⟨2, 0, 2, 3⟩ cache_2, place ⟨2, 6, 2, 4⟩ cache_2] = cache_10 := by
  decide +kernel

theorem load_entry_10 : entryAt 10 = entry_10 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_10 : CacheEquation 10 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(10 < 6)), load_entry_10]
  change forkRow [placeRow ⟨2, 0, 2, 3⟩ (denote cache_2), placeRow ⟨2, 6, 2, 4⟩ (denote cache_2)] = denote cache_10
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_10

theorem verified_row_11 : fork [place ⟨6, 4, 2, 5⟩ cache_6, place ⟨6, 6, 2, 3⟩ cache_6] = cache_11 := by
  decide +kernel

theorem load_entry_11 : entryAt 11 = entry_11 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_11 : CacheEquation 11 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(11 < 6)), load_entry_11]
  change forkRow [placeRow ⟨6, 4, 2, 5⟩ (denote cache_6), placeRow ⟨6, 6, 2, 3⟩ (denote cache_6)] = denote cache_11
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_11

theorem verified_row_12 : fork [place ⟨0, 6, 5, 4⟩ cache_0, place ⟨0, 0, 0, 3⟩ cache_0] = cache_12 := by
  decide +kernel

theorem load_entry_12 : entryAt 12 = entry_12 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_12 : CacheEquation 12 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(12 < 6)), load_entry_12]
  change forkRow [placeRow ⟨0, 6, 5, 4⟩ (denote cache_0), placeRow ⟨0, 0, 0, 3⟩ (denote cache_0)] = denote cache_12
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_12

theorem verified_row_13 : fork [place ⟨6, 6, 0, 3⟩ cache_6, place ⟨6, 4, 0, 5⟩ cache_6] = cache_13 := by
  decide +kernel

theorem load_entry_13 : entryAt 13 = entry_13 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_13 : CacheEquation 13 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(13 < 6)), load_entry_13]
  change forkRow [placeRow ⟨6, 6, 0, 3⟩ (denote cache_6), placeRow ⟨6, 4, 0, 5⟩ (denote cache_6)] = denote cache_13
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_13

theorem verified_row_14 : fork [place ⟨0, 6, 5, 4⟩ cache_0, place ⟨3, 6, 1, 4⟩ cache_3] = cache_14 := by
  decide +kernel

theorem load_entry_14 : entryAt 14 = entry_14 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_14 : CacheEquation 14 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(14 < 6)), load_entry_14]
  change forkRow [placeRow ⟨0, 6, 5, 4⟩ (denote cache_0), placeRow ⟨3, 6, 1, 4⟩ (denote cache_3)] = denote cache_14
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_14

theorem verified_row_15 : fork [place ⟨0, 6, 6, 4⟩ cache_0, place ⟨3, 6, 2, 4⟩ cache_3] = cache_15 := by
  decide +kernel

theorem load_entry_15 : entryAt 15 = entry_15 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_15 : CacheEquation 15 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(15 < 6)), load_entry_15]
  change forkRow [placeRow ⟨0, 6, 6, 4⟩ (denote cache_0), placeRow ⟨3, 6, 2, 4⟩ (denote cache_3)] = denote cache_15
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_15

theorem verified_row_16 : fork [place ⟨3, 6, 3, 4⟩ cache_3, place ⟨0, 6, 7, 4⟩ cache_0] = cache_16 := by
  decide +kernel

theorem load_entry_16 : entryAt 16 = entry_16 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_16 : CacheEquation 16 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(16 < 6)), load_entry_16]
  change forkRow [placeRow ⟨3, 6, 3, 4⟩ (denote cache_3), placeRow ⟨0, 6, 7, 4⟩ (denote cache_0)] = denote cache_16
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_16

theorem verified_row_17 : fork [place ⟨0, 6, 5, 4⟩ cache_0, place ⟨3, 0, 3, 3⟩ cache_3] = cache_17 := by
  decide +kernel

theorem load_entry_17 : entryAt 17 = entry_17 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_17 : CacheEquation 17 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(17 < 6)), load_entry_17]
  change forkRow [placeRow ⟨0, 6, 5, 4⟩ (denote cache_0), placeRow ⟨3, 0, 3, 3⟩ (denote cache_3)] = denote cache_17
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_17

theorem verified_row_18 : fork [place ⟨3, 6, 2, 4⟩ cache_3, place ⟨3, 0, 4, 3⟩ cache_3] = cache_18 := by
  decide +kernel

theorem load_entry_18 : entryAt 18 = entry_18 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_18 : CacheEquation 18 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(18 < 6)), load_entry_18]
  change forkRow [placeRow ⟨3, 6, 2, 4⟩ (denote cache_3), placeRow ⟨3, 0, 4, 3⟩ (denote cache_3)] = denote cache_18
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_18

theorem verified_row_19 : fork [place ⟨6, 4, 1, 5⟩ cache_6, place ⟨6, 0, 6, 5⟩ cache_6] = cache_19 := by
  decide +kernel

theorem load_entry_19 : entryAt 19 = entry_19 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_19 : CacheEquation 19 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(19 < 6)), load_entry_19]
  change forkRow [placeRow ⟨6, 4, 1, 5⟩ (denote cache_6), placeRow ⟨6, 0, 6, 5⟩ (denote cache_6)] = denote cache_19
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_19

theorem verified_row_20 : fork [place ⟨6, 4, 0, 5⟩ cache_6, place ⟨6, 0, 5, 5⟩ cache_6] = cache_20 := by
  decide +kernel

theorem load_entry_20 : entryAt 20 = entry_20 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_20 : CacheEquation 20 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(20 < 6)), load_entry_20]
  change forkRow [placeRow ⟨6, 4, 0, 5⟩ (denote cache_6), placeRow ⟨6, 0, 5, 5⟩ (denote cache_6)] = denote cache_20
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_20

theorem verified_row_21 : fork [place ⟨4, 6, 2, 3⟩ cache_4, place ⟨6, 0, 6, 5⟩ cache_6] = cache_21 := by
  decide +kernel

theorem load_entry_21 : entryAt 21 = entry_21 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_21 : CacheEquation 21 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(21 < 6)), load_entry_21]
  change forkRow [placeRow ⟨4, 6, 2, 3⟩ (denote cache_4), placeRow ⟨6, 0, 6, 5⟩ (denote cache_6)] = denote cache_21
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_21

theorem verified_row_22 : fork [place ⟨0, 6, 7, 5⟩ cache_0, place ⟨3, 0, 5, 4⟩ cache_3] = cache_22 := by
  decide +kernel

theorem load_entry_22 : entryAt 22 = entry_22 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_22 : CacheEquation 22 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(22 < 6)), load_entry_22]
  change forkRow [placeRow ⟨0, 6, 7, 5⟩ (denote cache_0), placeRow ⟨3, 0, 5, 4⟩ (denote cache_3)] = denote cache_22
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_22

theorem verified_row_23 : fork [place ⟨0, 6, 6, 4⟩ cache_0, place ⟨0, 0, 1, 3⟩ cache_0] = cache_23 := by
  decide +kernel

theorem load_entry_23 : entryAt 23 = entry_23 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_23 : CacheEquation 23 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(23 < 6)), load_entry_23]
  change forkRow [placeRow ⟨0, 6, 6, 4⟩ (denote cache_0), placeRow ⟨0, 0, 1, 3⟩ (denote cache_0)] = denote cache_23
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_23

theorem verified_row_24 : fork [place ⟨0, 0, 0, 3⟩ cache_0, place ⟨17, 0, 5, 4⟩ cache_17] = cache_24 := by
  decide +kernel

theorem load_entry_24 : entryAt 24 = entry_24 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_24 : CacheEquation 24 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(24 < 6)), load_entry_24]
  change forkRow [placeRow ⟨0, 0, 0, 3⟩ (denote cache_0), placeRow ⟨17, 0, 5, 4⟩ (denote cache_17)] = denote cache_24
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_24

theorem verified_row_25 : fork [place ⟨0, 0, 0, 3⟩ cache_0, place ⟨14, 0, 5, 4⟩ cache_14] = cache_25 := by
  decide +kernel

theorem load_entry_25 : entryAt 25 = entry_25 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_25 : CacheEquation 25 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(25 < 6)), load_entry_25]
  change forkRow [placeRow ⟨0, 0, 0, 3⟩ (denote cache_0), placeRow ⟨14, 0, 5, 4⟩ (denote cache_14)] = denote cache_25
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_25

theorem verified_row_26 : fork [place ⟨0, 4, 6, 4⟩ cache_0, place ⟨6, 0, 6, 5⟩ cache_6] = cache_26 := by
  decide +kernel

theorem load_entry_26 : entryAt 26 = entry_26 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_26 : CacheEquation 26 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(26 < 6)), load_entry_26]
  change forkRow [placeRow ⟨0, 4, 6, 4⟩ (denote cache_0), placeRow ⟨6, 0, 6, 5⟩ (denote cache_6)] = denote cache_26
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_26

theorem verified_row_27 : fork [place ⟨0, 6, 5, 4⟩ cache_0, place ⟨6, 4, 0, 5⟩ cache_6] = cache_27 := by
  decide +kernel

theorem load_entry_27 : entryAt 27 = entry_27 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_27 : CacheEquation 27 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(27 < 6)), load_entry_27]
  change forkRow [placeRow ⟨0, 6, 5, 4⟩ (denote cache_0), placeRow ⟨6, 4, 0, 5⟩ (denote cache_6)] = denote cache_27
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_27

theorem verified_row_28 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨0, 6, 6, 4⟩ cache_0] = cache_28 := by
  decide +kernel

theorem load_entry_28 : entryAt 28 = entry_28 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_28 : CacheEquation 28 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(28 < 6)), load_entry_28]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨0, 6, 6, 4⟩ (denote cache_0)] = denote cache_28
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_28

theorem verified_row_29 : fork [place ⟨1, 4, 7, 3⟩ cache_1, place ⟨6, 3, 4, 5⟩ cache_6] = cache_29 := by
  decide +kernel

theorem load_entry_29 : entryAt 29 = entry_29 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_29 : CacheEquation 29 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(29 < 6)), load_entry_29]
  change forkRow [placeRow ⟨1, 4, 7, 3⟩ (denote cache_1), placeRow ⟨6, 3, 4, 5⟩ (denote cache_6)] = denote cache_29
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_29

theorem verified_row_30 : fork [place ⟨0, 0, 1, 3⟩ cache_0, place ⟨14, 0, 6, 4⟩ cache_14] = cache_30 := by
  decide +kernel

theorem load_entry_30 : entryAt 30 = entry_30 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_30 : CacheEquation 30 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(30 < 6)), load_entry_30]
  change forkRow [placeRow ⟨0, 0, 1, 3⟩ (denote cache_0), placeRow ⟨14, 0, 6, 4⟩ (denote cache_14)] = denote cache_30
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_30

theorem verified_row_31 : fork [place ⟨0, 0, 1, 4⟩ cache_0, place ⟨17, 0, 6, 5⟩ cache_17] = cache_31 := by
  decide +kernel

theorem load_entry_31 : entryAt 31 = entry_31 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_31 : CacheEquation 31 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(31 < 6)), load_entry_31]
  change forkRow [placeRow ⟨0, 0, 1, 4⟩ (denote cache_0), placeRow ⟨17, 0, 6, 5⟩ (denote cache_17)] = denote cache_31
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_31

theorem verified_row_32 : fork [place ⟨0, 4, 8, 3⟩ cache_0, place ⟨6, 3, 4, 5⟩ cache_6] = cache_32 := by
  decide +kernel

theorem load_entry_32 : entryAt 32 = entry_32 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_32 : CacheEquation 32 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(32 < 6)), load_entry_32]
  change forkRow [placeRow ⟨0, 4, 8, 3⟩ (denote cache_0), placeRow ⟨6, 3, 4, 5⟩ (denote cache_6)] = denote cache_32
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_32

theorem verified_row_33 : fork [place ⟨0, 0, 2, 4⟩ cache_0, place ⟨17, 0, 7, 5⟩ cache_17] = cache_33 := by
  decide +kernel

theorem load_entry_33 : entryAt 33 = entry_33 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_33 : CacheEquation 33 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(33 < 6)), load_entry_33]
  change forkRow [placeRow ⟨0, 0, 2, 4⟩ (denote cache_0), placeRow ⟨17, 0, 7, 5⟩ (denote cache_17)] = denote cache_33
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_33

theorem verified_row_34 : fork [place ⟨6, 1, 4, 5⟩ cache_6, place ⟨1, 6, 5, 4⟩ cache_1] = cache_34 := by
  decide +kernel

theorem load_entry_34 : entryAt 34 = entry_34 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_34 : CacheEquation 34 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(34 < 6)), load_entry_34]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (denote cache_6), placeRow ⟨1, 6, 5, 4⟩ (denote cache_1)] = denote cache_34
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_34

theorem verified_row_35 : fork [place ⟨0, 0, 2, 4⟩ cache_0, place ⟨14, 0, 7, 5⟩ cache_14] = cache_35 := by
  decide +kernel

theorem load_entry_35 : entryAt 35 = entry_35 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_35 : CacheEquation 35 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(35 < 6)), load_entry_35]
  change forkRow [placeRow ⟨0, 0, 2, 4⟩ (denote cache_0), placeRow ⟨14, 0, 7, 5⟩ (denote cache_14)] = denote cache_35
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_35

theorem verified_row_36 : fork [place ⟨0, 0, 3, 4⟩ cache_0, place ⟨17, 0, 8, 5⟩ cache_17] = cache_36 := by
  decide +kernel

theorem load_entry_36 : entryAt 36 = entry_36 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_36 : CacheEquation 36 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(36 < 6)), load_entry_36]
  change forkRow [placeRow ⟨0, 0, 3, 4⟩ (denote cache_0), placeRow ⟨17, 0, 8, 5⟩ (denote cache_17)] = denote cache_36
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_36

theorem verified_row_37 : fork [place ⟨6, 3, 4, 5⟩ cache_6, place ⟨2, 4, 6, 3⟩ cache_2] = cache_37 := by
  decide +kernel

theorem load_entry_37 : entryAt 37 = entry_37 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_37 : CacheEquation 37 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(37 < 6)), load_entry_37]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (denote cache_6), placeRow ⟨2, 4, 6, 3⟩ (denote cache_2)] = denote cache_37
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_37

theorem verified_row_38 : fork [place ⟨3, 0, 3, 3⟩ cache_3, place ⟨16, 0, 2, 4⟩ cache_16] = cache_38 := by
  decide +kernel

theorem load_entry_38 : entryAt 38 = entry_38 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_38 : CacheEquation 38 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(38 < 6)), load_entry_38]
  change forkRow [placeRow ⟨3, 0, 3, 3⟩ (denote cache_3), placeRow ⟨16, 0, 2, 4⟩ (denote cache_16)] = denote cache_38
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_38

theorem verified_row_39 : fork [place ⟨0, 0, 1, 3⟩ cache_0, place ⟨17, 0, 6, 4⟩ cache_17] = cache_39 := by
  decide +kernel

theorem load_entry_39 : entryAt 39 = entry_39 := by
  rw [entryAt, table_getElem?_eq]
  decide +kernel

theorem cache_equation_39 : CacheEquation 39 := by
  rw [CacheEquation, dite_eq_right (by decide : ¬(39 < 6)), load_entry_39]
  change forkRow [placeRow ⟨0, 0, 1, 3⟩ (denote cache_0), placeRow ⟨17, 0, 6, 4⟩ (denote cache_17)] = denote cache_39
  simpa only [denote_fork, List.map_cons, List.map_nil, denote_place] using
    congrArg denote verified_row_39

end SnakyCertificate.Check

end OAI
