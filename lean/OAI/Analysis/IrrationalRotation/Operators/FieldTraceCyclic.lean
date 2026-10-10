import Mathlib

namespace OAI

open MeasureTheory Filter
open scoped InnerProductSpace

namespace Invariant233.FieldTraceCyclic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem hasSum_matrix_product (b : HilbertBasis ℤ ℂ E)
    (A B : E →L[ℂ] E) (k : ℤ) :
    HasSum (fun r : ℤ => inner ℂ (b k) (A (b r)) * inner ℂ (b r) (B (b k)))
      (inner ℂ (b k) (A (B (b k)))) := by
  simpa only [ContinuousLinearMap.adjoint_inner_left] using
    b.hasSum_inner_mul_inner ((ContinuousLinearMap.adjoint A) (b k)) (B (b k))

theorem summable_norm_matrix_product (b : HilbertBasis ℤ ℂ E)
    (A B : E →L[ℂ] E) (k : ℤ) :
    Summable (fun r : ℤ =>
      ‖inner ℂ (b k) (A (b r)) * inner ℂ (b r) (B (b k))‖) :=
  summable_norm_iff.mpr (hasSum_matrix_product b A B k).summable

theorem tsum_norm_matrix_product_le (b : HilbertBasis ℤ ℂ E)
    (A B : E →L[ℂ] E) (k : ℤ) :
    (∑' r : ℤ, ‖inner ℂ (b k) (A (b r)) * inner ℂ (b r) (B (b k))‖) ≤
      ‖A‖ * ‖B‖ := by
  have hc := lp.tsum_mul_le_mul_norm' (p := 2) (q := 2)
    (by simpa using Real.HolderConjugate.two_two)
    (b.repr ((ContinuousLinearMap.adjoint A) (b k))) (b.repr (B (b k)))
  simp only [HilbertBasis.repr_apply_apply, LinearIsometryEquiv.norm_map] at hc
  calc
    (∑' r : ℤ, ‖inner ℂ (b k) (A (b r)) * inner ℂ (b r) (B (b k))‖) =
        ∑' r : ℤ, ‖inner ℂ (b r) ((ContinuousLinearMap.adjoint A) (b k))‖ *
          ‖inner ℂ (b r) (B (b k))‖ := by
      apply tsum_congr
      intro r
      rw [norm_mul, ← ContinuousLinearMap.adjoint_inner_left, norm_inner_symm]
    _ ≤ ‖(ContinuousLinearMap.adjoint A) (b k)‖ * ‖B (b k)‖ := hc
    _ ≤ (‖ContinuousLinearMap.adjoint A‖ * ‖b k‖) * (‖B‖ * ‖b k‖) :=
      mul_le_mul ((ContinuousLinearMap.adjoint A).le_opNorm (b k))
        (B.le_opNorm (b k)) (norm_nonneg _) (by positivity)
    _ = ‖A‖ * ‖B‖ := by
      rw [ContinuousLinearMap.adjoint.norm_map, b.orthonormal.norm_eq_one]
      ring

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

theorem hasSum_integral_matrix_product (b : HilbertBasis ℤ ℂ E)
    (A B : Ω → E →L[ℂ] E)
    (hA : ∀ r : ℤ, AEStronglyMeasurable (fun x => A x (b r)) μ)
    (hB : ∀ r : ℤ, AEStronglyMeasurable (fun x => B x (b r)) μ)
    (CA CB : ℝ) (hCA : 0 ≤ CA)
    (hAbound : ∀ᵐ x ∂μ, ‖A x‖ ≤ CA) (hBbound : ∀ᵐ x ∂μ, ‖B x‖ ≤ CB)
    (k : ℤ) :
    HasSum (fun r : ℤ => ∫ x,
      inner ℂ (b k) (A x (b r)) * inner ℂ (b r) (B x (b k)) ∂μ)
      (∫ x, inner ℂ (b k) (A x (B x (b k))) ∂μ) := by
  let F : ℤ → Ω → ℂ := fun r x =>
    inner ℂ (b k) (A x (b r)) * inner ℂ (b r) (B x (b k))
  have hFm : ∀ r, AEStronglyMeasurable (F r) μ := by
    intro r
    exact (aestronglyMeasurable_const.inner (hA r)).mul
      (aestronglyMeasurable_const.inner (hB k))
  have hsumInt : Integrable (fun x => ∑' r, ‖F r x‖) μ := by
    apply (integrable_const (CA * CB)).mono' (AEStronglyMeasurable.tsum (fun r => (hFm r).norm))
    filter_upwards [hAbound, hBbound] with x hxA hxB
    rw [Real.norm_of_nonneg (tsum_nonneg (fun r => norm_nonneg (F r x)))]
    exact (tsum_norm_matrix_product_le b (A x) (B x) k).trans
      (mul_le_mul hxA hxB (norm_nonneg _) hCA)
  exact hasSum_integral_of_dominated_convergence
    (fun r x => ‖F r x‖) hFm (fun _ => ae_of_all _ (fun _ => le_rfl))
    (ae_of_all _ (fun x => summable_norm_matrix_product b (A x) (B x) k))
    hsumInt (ae_of_all _ (fun x => hasSum_matrix_product b (A x) (B x) k))

theorem integral_central_matrix_product_cyclic (b : HilbertBasis ℤ ℂ E)
    (A B : Ω → E →L[ℂ] E)
    (hA : ∀ r : ℤ, AEStronglyMeasurable (fun x => A x (b r)) μ)
    (hB : ∀ r : ℤ, AEStronglyMeasurable (fun x => B x (b r)) μ)
    (CA CB : ℝ) (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (hAbound : ∀ᵐ x ∂μ, ‖A x‖ ≤ CA) (hBbound : ∀ᵐ x ∂μ, ‖B x‖ ≤ CB)
    (σ : ℤ → Ω → Ω) (hσ : ∀ r, MeasurePreserving (σ r) μ μ)
    (hcovA : ∀ r k l : ℤ, ∀ᵐ x ∂μ,
      inner ℂ (b k) (A (σ r x) (b l)) = inner ℂ (b (k + r)) (A x (b (l + r))))
    (hcovB : ∀ r k l : ℤ, ∀ᵐ x ∂μ,
      inner ℂ (b k) (B (σ r x) (b l)) = inner ℂ (b (k + r)) (B x (b (l + r)))) :
    (∫ x, inner ℂ (b 0) (A x (B x (b 0))) ∂μ) =
      ∫ x, inner ℂ (b 0) (B x (A x (b 0))) ∂μ := by
  have hterm (r : ℤ) :
      (∫ x, inner ℂ (b 0) (A x (b r)) * inner ℂ (b r) (B x (b 0)) ∂μ) =
        ∫ x, inner ℂ (b 0) (B x (b (-r))) * inner ℂ (b (-r)) (A x (b 0)) ∂μ := by
    let f : Ω → ℂ := fun x =>
      inner ℂ (b 0) (B x (b (-r))) * inner ℂ (b (-r)) (A x (b 0))
    have hfm : AEStronglyMeasurable f μ :=
      (aestronglyMeasurable_const.inner (hB (-r))).mul
        (aestronglyMeasurable_const.inner (hA 0))
    have hm : AEStronglyMeasurable f (μ.map (σ r)) := by
      rw [(hσ r).map_eq]
      exact hfm
    calc
      (∫ x, inner ℂ (b 0) (A x (b r)) * inner ℂ (b r) (B x (b 0)) ∂μ) =
          ∫ x, f (σ r x) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hcovA r (-r) 0, hcovB r 0 (-r)] with x hxA hxB
        simp only [neg_add_cancel, zero_add] at hxA hxB
        dsimp [f]
        rw [hxA, hxB]
        exact mul_comm _ _
      _ = ∫ x, f x ∂μ := by
        simpa only [(hσ r).map_eq] using
          (integral_map (hσ r).measurable.aemeasurable hm).symm
  rw [← (hasSum_integral_matrix_product b A B hA hB CA CB hCA hAbound hBbound 0).tsum_eq,
    ← (hasSum_integral_matrix_product b B A hB hA CB CA hCB hBbound hAbound 0).tsum_eq]
  calc
    (∑' r : ℤ, ∫ x, inner ℂ (b 0) (A x (b r)) * inner ℂ (b r) (B x (b 0)) ∂μ) =
        ∑' r : ℤ, ∫ x, inner ℂ (b 0) (B x (b (-r))) * inner ℂ (b (-r)) (A x (b 0)) ∂μ :=
      tsum_congr hterm
    _ = ∑' r : ℤ, ∫ x, inner ℂ (b 0) (B x (b r)) * inner ℂ (b r) (A x (b 0)) ∂μ :=
      by
        simpa only [Equiv.neg_apply] using
          (Equiv.neg ℤ).tsum_eq (fun r : ℤ =>
            ∫ x, inner ℂ (b 0) (B x (b r)) * inner ℂ (b r) (A x (b 0)) ∂μ)

end Invariant233.FieldTraceCyclic

end OAI
