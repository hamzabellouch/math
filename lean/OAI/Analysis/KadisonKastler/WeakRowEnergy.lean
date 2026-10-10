import OAI.Analysis.KadisonKastler.RowEnergyBounds
import OAI.Analysis.KadisonKastler.WeakRowAction

namespace OAI

/-! Finite row energy sublevels are closed in the pointwise weak topology. -/

namespace KadisonKastler

noncomputable section

open Generator
open scoped Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem hilbert_norm_le_iff {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (v : E) {c : ℝ} (hc : 0 ≤ c) :
    ‖v‖ ≤ c ↔ ∀ w : E, ‖inner ℂ v w‖ ≤ c * ‖w‖ := by
  constructor
  · intro h w
    exact (norm_inner_le_norm v w).trans (mul_le_mul_of_nonneg_right h (norm_nonneg w))
  · intro h
    have hv := h v
    have hi : ‖inner ℂ v v‖ = ‖v‖ ^ 2 := by
      rw [← inner_self_re_eq_norm, inner_self_eq_norm_sq]
    rw [hi] at hv
    nlinarith [norm_nonneg v]

theorem rowEnergy_test_coefficient {M : VonNeumannAlgebra H} {c : ℝ}
    (F : BoundedWeakAlgebraMap M c) {ι : Type*} [Fintype ι]
    (r : ι → Algebra M) (ξ : H) (η : FiniteHilbert ι H) :
    inner ℂ (rowAdjointVector (fun i => F.map (r i)) ξ) η =
      ∑ i, boundedWeakAlgebraCoefficients F (r i, η i, ξ) := by
  simp only [PiLp.inner_apply, rowAdjointVector,
    boundedWeakAlgebraCoefficients]
  apply Finset.sum_congr rfl
  intro i _
  exact ContinuousLinearMap.adjoint_inner_left (F.map (r i) : H →L[ℂ] H) (η i) ξ

theorem isClosed_rowEnergy_le {M : VonNeumannAlgebra H} {c d : ℝ}
    (hd : 0 ≤ d) {ι : Type*} [Fintype ι] (r : ι → Algebra M) (ξ : H) :
    IsClosed {F : BoundedWeakAlgebraMap M c | rowEnergy F.map r ξ ≤ d} := by
  have he : {F : BoundedWeakAlgebraMap M c | rowEnergy F.map r ξ ≤ d} =
      ⋂ η : FiniteHilbert ι H, {F | ‖∑ i,
        boundedWeakAlgebraCoefficients F (r i, η i, ξ)‖ ≤ Real.sqrt d * ‖η‖} := by
    ext F
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    have hsq : rowEnergy F.map r ξ =
        ‖rowAdjointVector (fun i => F.map (r i)) ξ‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2]
      rfl
    have hn : rowEnergy F.map r ξ ≤ d ↔
        ‖rowAdjointVector (fun i => F.map (r i)) ξ‖ ≤ Real.sqrt d := by
      rw [hsq]
      have hs := Real.sq_sqrt hd
      have hp := Real.sqrt_nonneg d
      have hv := norm_nonneg (rowAdjointVector (fun i => F.map (r i)) ξ)
      constructor <;> intro h <;> nlinarith
    rw [hn, hilbert_norm_le_iff _ (Real.sqrt_nonneg d)]
    simp_rw [rowEnergy_test_coefficient]
  rw [he]
  apply isClosed_iInter
  intro η
  apply isClosed_le _ continuous_const
  apply Continuous.norm
  apply continuous_finsetSum
  intro i _
  have hcoeff : Continuous (boundedWeakAlgebraCoefficients (M := M) (c := c)) :=
    continuous_induced_dom
  exact (continuous_apply (r i, η i, ξ)).comp hcoeff

end

end KadisonKastler

end OAI
