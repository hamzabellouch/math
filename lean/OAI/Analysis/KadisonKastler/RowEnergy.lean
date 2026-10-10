import OAI.Analysis.KadisonKastler.RowVariance

namespace OAI

/-! Row energies and their decrease under normalized averaging. -/

namespace KadisonKastler

noncomputable section

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def rowEnergy {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι]
    (F : Algebra M →ₗ[ℂ] Algebra M) (r : ι → Algebra M) (ξ : H) : ℝ :=
  ∑ i, ‖(star (F (r i)) : H →L[ℂ] H) ξ‖ ^ 2

theorem rowEnergy_nonneg {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι]
    (F : Algebra M →ₗ[ℂ] Algebra M) (r : ι → Algebra M) (ξ : H) :
    0 ≤ rowEnergy F r ξ := Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem finiteRightAverage_star_apply {M : VonNeumannAlgebra H}
    {ι : Type*} [Fintype ι] (r : ι → Algebra M)
    (F : Algebra M →ₗ[ℂ] Algebra M) (a : Algebra M) (ξ : H) :
    (star (finiteRightAverage r F a) : H →L[ℂ] H) ξ =
      rowSynthesis r (fun i => (star (F (a * r i)) : H →L[ℂ] H) ξ) := by
  simp [finiteRightAverage_apply, rowSynthesis, star_mul]

theorem rowSynthesis_norm_sq_le {M : VonNeumannAlgebra H}
    {ι : Type*} [Fintype ι] (r : ι → Algebra M)
    (hr : ∑ i, r i * star (r i) = 1) (v : ι → H) :
    ‖rowSynthesis r v‖ ^ 2 ≤ ∑ i, ‖v i‖ ^ 2 := by
  have h := normalizedRow_variance r hr v
  have hpos : 0 ≤ ∑ i, ‖v i - (star (r i) : H →L[ℂ] H) (rowSynthesis r v)‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith

theorem rowEnergy_rightAverage_le {M : VonNeumannAlgebra H}
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : Algebra M →ₗ[ℂ] Algebra M) (r : ι → Algebra M) (s : κ → Algebra M)
    (hs : ∑ j, s j * star (s j) = 1) (ξ : H) :
    rowEnergy (finiteRightAverage s F) r ξ ≤
      rowEnergy F (fun ij : ι × κ => r ij.1 * s ij.2) ξ := by
  unfold rowEnergy
  rw [Fintype.sum_prod_type]
  apply Finset.sum_le_sum
  intro i _
  rw [finiteRightAverage_star_apply]
  exact rowSynthesis_norm_sq_le s hs _

theorem rowEnergy_rightAverage_variance {M : VonNeumannAlgebra H}
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : Algebra M →ₗ[ℂ] Algebra M) (r : ι → Algebra M) (s : κ → Algebra M)
    (hs : ∑ j, s j * star (s j) = 1) (ξ : H) :
    rowEnergy F (fun ij : ι × κ => r ij.1 * s ij.2) ξ -
      rowEnergy (finiteRightAverage s F) r ξ =
      ∑ i, ∑ j, ‖(star (F (r i * s j)) : H →L[ℂ] H) ξ -
        (star (s j) : H →L[ℂ] H)
          ((star (finiteRightAverage s F (r i)) : H →L[ℂ] H) ξ)‖ ^ 2 := by
  unfold rowEnergy
  rw [Fintype.sum_prod_type, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [finiteRightAverage_star_apply]
  exact (normalizedRow_variance s hs _).symm

end

end KadisonKastler

end OAI
