import OAI.Combinatorics.Ramsey.CycleClique.Construction.Patterns

namespace OAI

/-! Exact sizes of the canonical pattern domains in Table 1. -/

namespace CycleClique.Construction
theorem patternCount_5_3 : patternCount 5 3 = 4 := by
  unfold patternCount
  rw [pathPatterns_eq_fuel (Nat.le_refl _), pathPatternsFuel_length, patternNumberFuel_eq_shallow]
  decide

theorem patternCount_5_4 : patternCount 5 4 = 2 := by
  unfold patternCount
  rw [pathPatterns_eq_fuel (Nat.le_refl _), pathPatternsFuel_length, patternNumberFuel_eq_shallow]
  decide

theorem patternCount_5_5 : patternCount 5 5 = 1 := by
  unfold patternCount
  rw [pathPatterns_eq_fuel (Nat.le_refl _), pathPatternsFuel_length, patternNumberFuel_eq_shallow]
  decide

theorem patternCount_6_3 : patternCount 6 3 = 6 := by
  unfold patternCount
  rw [pathPatterns_eq_fuel (Nat.le_refl _), pathPatternsFuel_length, patternNumberFuel_eq_shallow]
  decide

theorem patternCount_6_4 : patternCount 6 4 = 5 := by
  unfold patternCount
  rw [pathPatterns_eq_fuel (Nat.le_refl _), pathPatternsFuel_length, patternNumberFuel_eq_shallow]
  decide

theorem patternCount_6_5 : patternCount 6 5 = 2 := by
  unfold patternCount
  rw [pathPatterns_eq_fuel (Nat.le_refl _), pathPatternsFuel_length, patternNumberFuel_eq_shallow]
  decide

theorem patternCount_6_6 : patternCount 6 6 = 1 := by
  unfold patternCount
  rw [pathPatterns_eq_fuel (Nat.le_refl _), pathPatternsFuel_length, patternNumberFuel_eq_shallow]
  decide

theorem patternCount_7_3 : patternCount 7 3 = 9 := by
  unfold patternCount
  rw [pathPatterns_eq_fuel (Nat.le_refl _), pathPatternsFuel_length, patternNumberFuel_eq_shallow]
  decide

theorem patternCount_7_4 : patternCount 7 4 = 9 := by
  unfold patternCount
  rw [pathPatterns_eq_fuel (Nat.le_refl _), pathPatternsFuel_length, patternNumberFuel_eq_shallow]
  decide

theorem patternCount_7_5 : patternCount 7 5 = 5 := by
  unfold patternCount
  rw [pathPatterns_eq_fuel (Nat.le_refl _), pathPatternsFuel_length, patternNumberFuel_eq_shallow]
  decide

theorem patternCount_7_6 : patternCount 7 6 = 2 := by
  unfold patternCount
  rw [pathPatterns_eq_fuel (Nat.le_refl _), pathPatternsFuel_length, patternNumberFuel_eq_shallow]
  decide

theorem patternCount_7_7 : patternCount 7 7 = 1 := by
  unfold patternCount
  rw [pathPatterns_eq_fuel (Nat.le_refl _), pathPatternsFuel_length, patternNumberFuel_eq_shallow]
  decide

theorem patternCount_8_4 : patternCount 8 4 = 16 := by
  unfold patternCount
  rw [pathPatterns_eq_fuel (Nat.le_refl _), pathPatternsFuel_length, patternNumberFuel_eq_shallow]
  decide

theorem patternCount_8_5 : patternCount 8 5 = 10 := by
  unfold patternCount
  rw [pathPatterns_eq_fuel (Nat.le_refl _), pathPatternsFuel_length, patternNumberFuel_eq_shallow]
  decide

theorem patternCount_8_6 : patternCount 8 6 = 5 := by
  unfold patternCount
  rw [pathPatterns_eq_fuel (Nat.le_refl _), pathPatternsFuel_length, patternNumberFuel_eq_shallow]
  decide

theorem patternCount_8_7 : patternCount 8 7 = 2 := by
  unfold patternCount
  rw [pathPatterns_eq_fuel (Nat.le_refl _), pathPatternsFuel_length, patternNumberFuel_eq_shallow]
  decide

theorem patternCount_8_8 : patternCount 8 8 = 1 := by
  unfold patternCount
  rw [pathPatterns_eq_fuel (Nat.le_refl _), pathPatternsFuel_length, patternNumberFuel_eq_shallow]
  decide

theorem patternCount_9_4 : patternCount 9 4 = 25 := by
  unfold patternCount
  rw [pathPatterns_eq_fuel (Nat.le_refl _), pathPatternsFuel_length, patternNumberFuel_eq_shallow]
  decide

theorem patternCount_9_5 : patternCount 9 5 = 20 := by
  unfold patternCount
  rw [pathPatterns_eq_fuel (Nat.le_refl _), pathPatternsFuel_length, patternNumberFuel_eq_shallow]
  decide

theorem patternCount_9_6 : patternCount 9 6 = 11 := by
  unfold patternCount
  rw [pathPatterns_eq_fuel (Nat.le_refl _), pathPatternsFuel_length, patternNumberFuel_eq_shallow]
  decide

theorem patternCount_9_7 : patternCount 9 7 = 5 := by
  unfold patternCount
  rw [pathPatterns_eq_fuel (Nat.le_refl _), pathPatternsFuel_length, patternNumberFuel_eq_shallow]
  decide

theorem patternCount_9_8 : patternCount 9 8 = 2 := by
  unfold patternCount
  rw [pathPatterns_eq_fuel (Nat.le_refl _), pathPatternsFuel_length, patternNumberFuel_eq_shallow]
  decide

theorem patternCount_10_5 : patternCount 10 5 = 35 := by
  unfold patternCount
  rw [pathPatterns_eq_fuel (Nat.le_refl _), pathPatternsFuel_length, patternNumberFuel_eq_shallow]
  decide

theorem patternCount_10_6 : patternCount 10 6 = 24 := by
  unfold patternCount
  rw [pathPatterns_eq_fuel (Nat.le_refl _), pathPatternsFuel_length, patternNumberFuel_eq_shallow]
  decide

theorem patternCount_10_7 : patternCount 10 7 = 11 := by
  unfold patternCount
  rw [pathPatterns_eq_fuel (Nat.le_refl _), pathPatternsFuel_length, patternNumberFuel_eq_shallow]
  decide

theorem patternCount_10_8 : patternCount 10 8 = 5 := by
  unfold patternCount
  rw [pathPatterns_eq_fuel (Nat.le_refl _), pathPatternsFuel_length, patternNumberFuel_eq_shallow]
  decide

theorem patternCount_11_5 : patternCount 11 5 = 60 := by
  unfold patternCount
  rw [pathPatterns_eq_fuel (Nat.le_refl _), pathPatternsFuel_length, patternNumberFuel_eq_shallow]
  decide

theorem patternCount_11_6 : patternCount 11 6 = 46 := by
  unfold patternCount
  rw [pathPatterns_eq_fuel (Nat.le_refl _), pathPatternsFuel_length, patternNumberFuel_eq_shallow]
  decide

theorem patternCount_11_7 : patternCount 11 7 = 25 := by
  unfold patternCount
  rw [pathPatterns_eq_fuel (Nat.le_refl _), pathPatternsFuel_length, patternNumberFuel_eq_shallow]
  decide

theorem patternCount_11_8 : patternCount 11 8 = 11 := by
  unfold patternCount
  rw [pathPatterns_eq_fuel (Nat.le_refl _), pathPatternsFuel_length, patternNumberFuel_eq_shallow]
  decide

theorem patternCount_12_6 : patternCount 12 6 = 87 := by
  unfold patternCount
  rw [pathPatterns_eq_fuel (Nat.le_refl _), pathPatternsFuel_length, patternNumberFuel_eq_shallow]
  decide

theorem patternCount_12_7 : patternCount 12 7 = 51 := by
  unfold patternCount
  rw [pathPatterns_eq_fuel (Nat.le_refl _), pathPatternsFuel_length, patternNumberFuel_eq_shallow]
  decide

theorem patternCount_12_8 : patternCount 12 8 = 26 := by
  unfold patternCount
  rw [pathPatterns_eq_fuel (Nat.le_refl _), pathPatternsFuel_length, patternNumberFuel_eq_shallow]
  decide

theorem patternCount_13_6 : patternCount 13 6 = 152 := by
  unfold patternCount
  rw [pathPatterns_eq_fuel (Nat.le_refl _), pathPatternsFuel_length, patternNumberFuel_eq_shallow]
  decide

theorem patternCount_13_7 : patternCount 13 7 = 104 := by
  unfold patternCount
  rw [pathPatterns_eq_fuel (Nat.le_refl _), pathPatternsFuel_length, patternNumberFuel_eq_shallow]
  decide

theorem patternCount_13_8 : patternCount 13 8 = 55 := by
  unfold patternCount
  rw [pathPatterns_eq_fuel (Nat.le_refl _), pathPatternsFuel_length, patternNumberFuel_eq_shallow]
  decide

theorem patternCount_14_7 : patternCount 14 7 = 197 := by
  unfold patternCount
  rw [pathPatterns_eq_fuel (Nat.le_refl _), pathPatternsFuel_length, patternNumberFuel_eq_shallow]
  decide

theorem patternCount_14_8 : patternCount 14 8 = 118 := by
  unfold patternCount
  rw [pathPatterns_eq_fuel (Nat.le_refl _), pathPatternsFuel_length, patternNumberFuel_eq_shallow]
  decide

theorem patternCount_15_7 : patternCount 15 7 = 364 := by
  unfold patternCount
  rw [pathPatterns_eq_fuel (Nat.le_refl _), pathPatternsFuel_length, patternNumberFuel_eq_shallow]
  decide

theorem patternCount_15_8 : patternCount 15 8 = 237 := by
  unfold patternCount
  rw [pathPatterns_eq_fuel (Nat.le_refl _), pathPatternsFuel_length, patternNumberFuel_eq_shallow]
  decide

theorem patternCount_16_8 : patternCount 16 8 = 468 := by
  unfold patternCount
  rw [pathPatterns_eq_fuel (Nat.le_refl _), pathPatternsFuel_length, patternNumberFuel_eq_shallow]
  decide

theorem patternCount_17_8 : patternCount 17 8 = 879 := by
  unfold patternCount
  rw [pathPatterns_eq_fuel (Nat.le_refl _), pathPatternsFuel_length, patternNumberFuel_eq_shallow]
  decide

end CycleClique.Construction

end OAI
