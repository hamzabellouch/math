import OAI.Analysis.KadisonKastler.RowVectorEstimate

namespace OAI

/-! The exact Hilbert-space variance of a normalized operator row. -/

namespace KadisonKastler

noncomputable section

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def rowSynthesis {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι]
    (r : ι → Algebra M) (v : ι → H) : H := ∑ i, (r i : H →L[ℂ] H) (v i)

theorem rowSynthesis_inner {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι]
    (r : ι → Algebra M) (v : ι → H) (η : H) :
    ∑ i, inner ℂ ((star (r i) : H →L[ℂ] H) η) (v i) =
      inner ℂ η (rowSynthesis r v) := by
  simp only [rowSynthesis, inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact ContinuousLinearMap.adjoint_inner_left (r i : H →L[ℂ] H) (v i) η

theorem normalizedRow_variance {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι]
    (r : ι → Algebra M) (hr : ∑ i, r i * star (r i) = 1) (v : ι → H) :
    ∑ i, ‖v i - (star (r i) : H →L[ℂ] H) (rowSynthesis r v)‖ ^ 2 =
      (∑ i, ‖v i‖ ^ 2) - ‖rowSynthesis r v‖ ^ 2 := by
  let η := rowSynthesis r v
  have hη : (inner ℂ η η).re = ‖η‖ ^ 2 := by
    simpa only [RCLike.re_eq_complex_re] using (norm_sq_eq_re_inner (𝕜 := ℂ) η).symm
  have hsq : ∑ i, ‖(star (r i) : H →L[ℂ] H) η‖ ^ 2 = ‖η‖ ^ 2 := by
    have h := rowAdjointVector_norm_sq r η
    rw [hr] at h
    simpa only [PiLp.norm_sq_eq_of_L2, rowAdjointVector, PiLp.toLp_apply,
      OneMemClass.coe_one, one_apply_eq_self, hη] using h
  have hi : ∑ i, (inner ℂ (v i) ((star (r i) : H →L[ℂ] H) η)).re = ‖η‖ ^ 2 := by
    have h := congrArg Complex.re (rowSynthesis_inner r v η)
    have hsum : (∑ i, inner ℂ ((star (r i) : H →L[ℂ] H) η) (v i)).re =
        ∑ i, (inner ℂ ((star (r i) : H →L[ℂ] H) η) (v i)).re := by
      exact map_sum Complex.reCLM _ _
    rw [hsum] at h
    calc
      _ = ∑ i, (inner ℂ ((star (r i) : H →L[ℂ] H) η) (v i)).re := by
        apply Finset.sum_congr rfl
        intro i _
        simpa only [RCLike.re_eq_complex_re] using
          (inner_re_symm (𝕜 := ℂ) (v i) ((star (r i) : H →L[ℂ] H) η))
      _ = ‖η‖ ^ 2 := by
        change _ = ‖rowSynthesis r v‖ ^ 2
        exact h.trans hη
  change (∑ i, ‖v i - (star (r i) : H →L[ℂ] H) η‖ ^ 2) = _
  simp_rw [norm_sub_sq (𝕜 := ℂ)]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hsq]
  change (∑ i, ‖v i‖ ^ 2) - 2 * (∑ i,
    (inner ℂ (v i) ((star (r i) : H →L[ℂ] H) η)).re) + ‖η‖ ^ 2 = _
  rw [hi]
  ring

end

end KadisonKastler

end OAI
