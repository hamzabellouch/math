import OAI.NumberTheory.Ostmann.Characters.CharacterParameterChoice

namespace OAI

/-! # Uniform depth choices for the actual character endpoint construction -/
namespace Ostmann
open Filter

/-- The same fixed gap also pays the explicit nonanchor comparison margin. -/
theorem character_strong_gap_choice (a Ctotal Aend Bword Cdy ε : ℝ) :
    ∃ B : ℝ, 1 ≤ B ∧ 2 * (Aend + 2 * Bword + 3) + 5 ≤ B ∧
      2 * ((2 * Real.log (3 / a) + 3 + 2 * Ctotal) +
        (Aend + 2 * Bword + 1) + 2) ≤ B ∧
      2 * (Aend + 2 * Bword + 3) +
        (Cdy / a + max (Real.log 3) 0 + ε) + Real.log 2 + 6 ≤ B + 20 * Real.log a := by
  obtain ⟨B, hB, hrepeat, hanchor⟩ := character_gap_choice a Ctotal Aend Bword Cdy ε
  let B' := max B (2 * (Aend + 2 * Bword + 3) + 5)
  have hBB : B ≤ B' := le_max_left _ _
  exact ⟨B', hB.trans hBB, le_max_right _ _, hrepeat.trans hBB, by linarith only [hanchor, hBB]⟩

/-- This cutoff includes the progression-input constant and strict `z > 1`;
all bounds hold for every later depth, before the rich block chooses one. -/
theorem character_complete_depth_cutoff (c δ Cmass Cfinal B B₁ C₀ : ℝ)
    (hc : 0 < c) (hδ : 0 < δ) (hCmass : 0 ≤ Cmass) (hC₀ : 0 < C₀) (Kmin : ℕ) :
    ∃ K : ℕ, Kmin ≤ K ∧ 20000 ≤ K ∧ ∀ k : ℕ, K ≤ k →
      1 < cellRoleScale k ∧ C₀ ≤ Real.exp ((k : ℝ) / 10000) ∧
      Cfinal + (B + 20 * Real.log (cellRoleScale k) + 1) + 2 * B₁ + 1 ≤
        ((k - 1 : ℕ) : ℝ) * Real.log 2 - 1 ∧
      4 * Cmass *
        (characterTargetLabelBound c δ k + (k + 1) + (k + 1) : ℕ) ≤ cellRoleScale k := by
  obtain ⟨K₀, hK₀⟩ := exists_nat_ge (10000 * Real.log C₀)
  obtain ⟨K, hK, hdepth⟩ := character_depth_and_mass_budget c δ Cmass Cfinal B B₁ hc hδ hCmass
    (max Kmin (max 20000 K₀))
  refine ⟨K, (le_max_left _ _).trans hK,
    (le_max_left _ _).trans ((le_max_right _ _).trans hK), ?_⟩
  intro k hk
  obtain ⟨hk1, _, hentropy, hmass⟩ := hdepth k hk
  have hscale : 1 < cellRoleScale k := by
    apply Real.one_lt_exp_iff.mpr
    unfold cellRoleEpsilon
    have hkpos : (0 : ℝ) < k := by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 1) hk1
    positivity
  have hK₀k : K₀ ≤ k :=
    (le_max_right 20000 K₀).trans ((le_max_right Kmin _).trans (hK.trans hk))
  have hkR : (K₀ : ℝ) ≤ k := by exact_mod_cast hK₀k
  have hlog : Real.log C₀ ≤ (k : ℝ) / 10000 := by linarith only [hK₀, hkR]
  have hC : C₀ ≤ Real.exp ((k : ℝ) / 10000) :=
    (Real.log_le_iff_le_exp hC₀).mp hlog
  exact ⟨hscale, hC, hentropy, hmass⟩

end Ostmann

end OAI
