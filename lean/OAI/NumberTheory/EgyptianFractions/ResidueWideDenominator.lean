import OAI.NumberTheory.EgyptianFractions.ResidueDenominator

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337.ResidueConstruction

/-- The wide prime pool fits the same auxiliary-denominator size budget. -/
theorem residue_size_budget_wide {S : ℝ} {m a : ℕ}
    (hlog : 1 ≤ Real.log S) (hlarge : 100 * Real.log S ≤ S)
    (hmLower : S - Real.log S ≤ (m : ℝ) * Real.log S)
    (hmUpper : (m : ℝ) * Real.log S ≤ S)
    (ha : (a : ℝ) * Real.log 2 ≤ 100000 * Real.log S + Real.log 2) :
    S < (m : ℝ) * (100 * Real.log S) ∧
      (a : ℝ) * Real.log 2 + (2 * (1000 : ℝ) + 1) * (m : ℝ) *
        (101 * Real.log S) ≤ 204204 * S ∧
      (m : ℝ) * (101 * Real.log S) ≤ 101 * S := by
  have htwo : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- PNT-free factor-window variant of the residue denominator construction. -/
theorem construct_residue_denominator_wide {m : ℕ} (p : Fin m → ℕ)
    (q : Fin 1000 → Fin m → Fin 2 → ℕ) (hp : ∀ j, 0 < p j)
    (hq : ∀ i j e, 0 < q i j e) {S : ℝ}
    (hS : 1 ≤ S) (hlog : 1 ≤ Real.log S) (hlarge : 100 * Real.log S ≤ S)
    (hmLower : S - Real.log S ≤ (m : ℝ) * Real.log S)
    (hmUpper : (m : ℝ) * Real.log S ≤ S)
    (hpL : ∀ j, 100 * Real.log S ≤ Real.log (p j : ℝ))
    (hpU : ∀ j, Real.log (p j : ℝ) ≤ 101 * Real.log S)
    (hqU : ∀ i j e, Real.log (q i j e : ℝ) ≤ 101 * Real.log S) :
    ∃ M : ℕ, Real.exp S < (M : ℝ) ∧ (M : ℝ) ≤ Real.exp (204204 * S) ∧
      2 ^ ⌈100000 * Real.log S / Real.log 2⌉₊ ∣ M ∧
      (∀ I : Fin m → Fin 2, subsetEntry p I ∣ M ∧ 1 ≤ subsetEntry p I ∧
        (subsetEntry p I : ℝ) ≤ Real.exp (101 * S)) ∧
      (∀ i (I : Fin m → Fin 2), pairedEntry (q i) I ∣ M ∧ 1 ≤ pairedEntry (q i) I ∧
        (pairedEntry (q i) I : ℝ) ≤ Real.exp (101 * S)) := by
  obtain ⟨a, hcut, ha⟩ := exists_binary_cutoff hS 100000
  norm_num only [Nat.cast_ofNat] at ha
  obtain ⟨hLower, hUpper, hEntry⟩ := residue_size_budget_wide hlog hlarge hmLower hmUpper ha
  obtain ⟨hMl, hMu⟩ := auxiliaryDenominator_exp_bounds a p q hp hq S
    (100 * Real.log S) (101 * Real.log S) 204204
    hpL hpU hqU hLower (by simpa using hUpper)
  refine ⟨auxiliaryDenominator a p q, hMl, hMu, ?_, ?_, ?_⟩
  · simpa using ceiling_binary_factor_dvd_auxiliary a 100000 p q (by linarith : 0 < S) hcut
  · intro I
    have hpos := subsetEntry_pos p hp I
    refine ⟨subsetEntry_dvd_auxiliary a p q I, hpos, ?_⟩
    calc
      (subsetEntry p I : ℝ) = Real.exp (Real.log (subsetEntry p I : ℝ)) :=
        (Real.exp_log (by exact_mod_cast hpos)).symm
      _ ≤ Real.exp (101 * S) := Real.exp_le_exp.mpr
        ((log_subsetEntry_le p hp I _ (by positivity) hpU).trans hEntry)
  · intro i I
    have hpos := pairedEntry_pos (q i) (hq i) I
    refine ⟨pairedEntry_dvd_auxiliary a p q i I, hpos, ?_⟩
    calc
      (pairedEntry (q i) I : ℝ) = Real.exp (Real.log (pairedEntry (q i) I : ℝ)) :=
        (Real.exp_log (by exact_mod_cast hpos)).symm
      _ ≤ Real.exp (101 * S) := Real.exp_le_exp.mpr
        ((log_pairedEntry_le (q i) (hq i) I _ (hqU i)).trans hEntry)

end Problem337.ResidueConstruction

end

end OAI
