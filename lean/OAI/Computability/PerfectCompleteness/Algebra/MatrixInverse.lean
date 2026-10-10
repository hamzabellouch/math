import OAI.Computability.PerfectCompleteness.Foundations.GlobalityLemmas

namespace OAI

section

namespace PerfectCompleteness.MatrixInverse

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Fourier.MatrixNoise UniqueGamesTheorem.Fourier.MatrixRestrictions
open UniqueGamesTheorem.Fourier.MatrixLevelBridge
open UniqueGamesTheorem.Appendix.LevelInequality UniqueGamesTheorem.Appendix.RankLevelFilter

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Finite E] [Fintype F] [Fintype (E →ₗ[F2] F2)]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

def noiseEnergy (f : (E →ₗ[F2] F) → ℝ) : ℝ :=
  𝔼 X, f X * linearRealNoiseOperator (fun _ : F => (Fintype.card F : ℝ)⁻¹) f X

omit [Finite E] in
theorem noiseEnergy_eq (f : (E →ₗ[F2] F) → ℝ) :
    noiseEnergy f = ∑ S : F →ₗ[F2] E, node (frequencyRank S) * linearCoeff f S ^ 2 := by
  unfold noiseEnergy
  rw [linearRealNoiseOperator_energy]
  apply Finset.sum_congr rfl
  intro S _
  rw [linearNoiseEigenvalue_uniform, node_eq_inv_pow]
  rfl

omit [Finite E] in
theorem noiseEnergy_le_cutoff (r : Nat) (f : (E →ₗ[F2] F) → ℝ) :
    noiseEnergy f ≤ rankCutoffEnergy r f + node (r + 1) * (𝔼 X, f X ^ 2) := by
  rw [noiseEnergy_eq]
  calc
    _ ≤ ∑ S : F →ₗ[F2] E,
        ((if frequencyRank S ≤ r then linearCoeff f S ^ 2 else 0) +
          node (r + 1) * linearCoeff f S ^ 2) := by
      apply Finset.sum_le_sum
      intro S _
      by_cases h : frequencyRank S ≤ r
      · rw [ite_eq_left h]
        have h₁ := mul_le_mul_of_nonneg_right (node_le_one (frequencyRank S))
          (sq_nonneg (linearCoeff f S))
        have h₂ := mul_nonneg (node_pos (r + 1)).le (sq_nonneg (linearCoeff f S))
        linarith
      · rw [ite_eq_right h, zero_add]
        exact mul_le_mul_of_nonneg_right
          (node_antitone (Nat.succ_le_of_lt (Nat.lt_of_not_ge h))) (sq_nonneg _)
    _ = rankCutoffEnergy r f + node (r + 1) * (𝔼 X, f X ^ 2) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, linear_parseval]
      simp only [rankCutoffEnergy, Finset.sum_filter]

theorem noiseEnergy_le_of_global (r : Nat) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (f : (E →ₗ[F2] F) → ℝ) (hf : IsBoolean f)
    (hg : IsRestrictionGlobal f r ρ) :
    noiseEnergy f ≤ (levelCutoffConstant r ρ + node (r + 1)) * (𝔼 X, f X ^ 2) := by
  have hcut := rankCutoffEnergy_le_of_theorem23
    (UniqueGamesTheorem.Appendix.LevelTheorem.theorem23 (E := E) (F := F)) f r ρ hρ hρ1 hf hg
  calc
    noiseEnergy f ≤ rankCutoffEnergy r f + node (r + 1) * (𝔼 X, f X ^ 2) :=
      noiseEnergy_le_cutoff r f
    _ ≤ levelCutoffConstant r ρ * (𝔼 X, f X ^ 2) +
        node (r + 1) * (𝔼 X, f X ^ 2) := add_le_add hcut (le_refl _)
    _ = _ := (add_mul _ _ _).symm

theorem exists_dense_restriction (r : Nat) (ρ η : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hconstants : levelCutoffConstant r ρ + node (r + 1) < η)
    (f : (E →ₗ[F2] F) → ℝ) (hf : IsBoolean f)
    (hpositive : 0 < 𝔼 X, f X ^ 2)
    (hretention : η * (𝔼 X, f X ^ 2) ≤ noiseEnergy f) :
    ∃ (W : Submodule F2 E) (C' : Submodule F2 F) (T : E →ₗ[F2] F),
      order W C' ≤ r ∧ ρ < (𝔼 N, restrict f W C' T N) := by
  by_contra hnone
  have hg : IsRestrictionGlobal f r ρ := by
    apply (boolean_global_iff_density f hf r ρ).mpr
    intro W C' T horder
    apply le_of_not_gt
    intro hdense
    exact hnone ⟨W, C', T, horder, hdense⟩
  have hbound := noiseEnergy_le_of_global r ρ hρ hρ1 f hf hg
  have hstrict := mul_lt_mul_of_pos_right hconstants hpositive
  exact (not_lt_of_ge (hretention.trans hbound)) hstrict

theorem exists_dense_restriction_of_family {Y : Type*} [Fintype Y]
    (r : Nat) (ρ η : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hconstants : levelCutoffConstant r ρ + node (r + 1) < η)
    (f : Y → (E →ₗ[F2] F) → ℝ) (hf : ∀ y, IsBoolean (f y))
    (hmass : (∑ y, 𝔼 X, f y X ^ 2) ≤ 1)
    (hretention : η ≤ ∑ y, noiseEnergy (f y)) :
    ∃ (y : Y) (W : Submodule F2 E) (C' : Submodule F2 F) (T : E →ₗ[F2] F),
      order W C' ≤ r ∧ ρ < (𝔼 N, restrict (f y) W C' T N) := by
  by_contra hnone
  have hg (y : Y) : IsRestrictionGlobal (f y) r ρ := by
    apply (boolean_global_iff_density (f y) (hf y) r ρ).mpr
    intro W C' T horder
    apply le_of_not_gt
    intro hdense
    exact hnone ⟨y, W, C', T, horder, hdense⟩
  have hbound : (∑ y, noiseEnergy (f y)) ≤
      (levelCutoffConstant r ρ + node (r + 1)) * (∑ y, 𝔼 X, f y X ^ 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun y _ => noiseEnergy_le_of_global r ρ hρ hρ1 (f y) (hf y) (hg y)
  have hnonneg : 0 ≤ levelCutoffConstant r ρ + node (r + 1) :=
    add_nonneg (levelCutoffConstant_nonneg r ρ hρ.le) (node_pos _).le
  have hbound' := hbound.trans (mul_le_mul_of_nonneg_left hmass hnonneg)
  simp only [mul_one] at hbound'
  exact (not_lt_of_ge (hretention.trans hbound')) hconstants

end
end PerfectCompleteness.MatrixInverse

end

end OAI
