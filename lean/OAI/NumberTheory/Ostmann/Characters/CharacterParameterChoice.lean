import OAI.NumberTheory.Ostmann.Characters.CharacterSelectionBudget
import OAI.NumberTheory.Ostmann.Construction.InitialGapRate

namespace OAI

/-! # Choose the character gap before the depth and the growing word length -/
namespace Ostmann

/-- The initial repeat loss and density-rescaled anchor energy require one
fixed gap constant. It does not depend on the later depth or selected cells. -/
theorem character_gap_choice (a Ctotal Aend Bword Cdy ε : ℝ) :
    ∃ B : ℝ, 1 ≤ B ∧
      2 * ((2 * Real.log (3 / a) + 3 + 2 * Ctotal) +
        (Aend + 2 * Bword + 1) + 2) ≤ B ∧
      2 * (Aend + 2 * Bword + 3) +
        (Cdy / a + max (Real.log 3) 0 + ε) + Real.log 2 + 6 ≤ B + 20 * Real.log a := by
  let Brepeat := 2 * ((2 * Real.log (3 / a) + 3 + 2 * Ctotal) +
    (Aend + 2 * Bword + 1) + 2)
  let Banchor := 2 * (Aend + 2 * Bword + 3) +
    (Cdy / a + max (Real.log 3) 0 + ε) + Real.log 2 + 6 - 20 * Real.log a
  refine ⟨max 1 (max Brepeat Banchor), le_max_left _ _, ?_, ?_⟩
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · have hh := (le_max_right Brepeat Banchor).trans (le_max_right 1 (max Brepeat Banchor))
    dsimp only [Banchor] at hh
    linarith

/-- The same depth threshold pays for every label, pivot normalizer and
nonbulk cost, while leaving the final permutation-entropy margin. -/
theorem character_depth_and_mass_budget (c δ Cmass Cfinal B B₁ : ℝ)
    (hc : 0 < c) (hδ : 0 < δ) (_hCmass : 0 ≤ Cmass) (Kmin : ℕ) :
    ∃ K : ℕ, Kmin ≤ K ∧ ∀ k : ℕ, K ≤ k →
      1 ≤ k ∧ 1 ≤ cellRoleScale k ∧
      Cfinal + (B + 20 * Real.log (cellRoleScale k) + 1) + 2 * B₁ + 1 ≤
        ((k - 1 : ℕ) : ℝ) * Real.log 2 - 1 ∧
      4 * Cmass *
        (characterTargetLabelBound c δ k + (k + 1) + (k + 1) : ℕ) ≤ cellRoleScale k := by
  let C := Cfinal + B + 2 * B₁ + 2 + Real.log 2
  let b := (4 * max Cmass 1)⁻¹
  have hb : 0 < b := by dsimp [b]; positivity
  obtain ⟨K, hK, hh⟩ := character_selection_depth c δ C b hc hδ hb Kmin
  refine ⟨K, hK, fun k hk => ?_⟩
  obtain ⟨hk1, hz, hentropy, hcount⟩ := hh k hk
  refine ⟨hk1, hz, ?_, ?_⟩
  · have hkcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub hk1, Nat.cast_one]
    rw [hkcast]
    dsimp only [C] at hentropy
    nlinarith only [hentropy]
  · have hmax : 0 < 4 * max Cmass 1 := by positivity
    have hcount' :
        (characterTargetLabelBound c δ k + (k + 1) + (k + 1) : ℕ) ≤
          cellRoleScale k / (4 * max Cmass 1) := by
      simpa only [b, div_eq_mul_inv, mul_comm] using hcount
    have hprod := (le_div_iff₀ hmax).mp hcount'
    have hcmax : 4 * Cmass ≤ 4 * max Cmass 1 := by
      exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)
    have hnat : (0 : ℝ) ≤ (characterTargetLabelBound c δ k + (k + 1) + (k + 1) : ℕ) :=
      Nat.cast_nonneg _
    nlinarith only [hprod, mul_le_mul_of_nonneg_right hcmax hnat]

end Ostmann

end OAI
