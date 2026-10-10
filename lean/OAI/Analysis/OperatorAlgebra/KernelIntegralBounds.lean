import OAI.Analysis.OperatorAlgebra.ScalarKernelPairing

namespace OAI

/-! Product-integrable bounds and a measure-preserving change of variables
for the scalar kernels used in crossed-product reconstruction. -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace

namespace WeakPureInfiniteness

lemma integrable_weighted_scalar_kernel (u v : ℝ → ℂ) (hu : Integrable u) (hv : Integrable v)
    (K : ℝ × ℝ → ℂ) (hK : Continuous K) (C : ℝ) (hC : ∀ p, ‖K p‖ ≤ C) :
    Integrable (fun p : ℝ × ℝ => star (u p.1) * v p.2 * K p) (volume.prod volume) := by
  apply ((hu.norm.mul_prod hv.norm).mul_const C).mono'
    ((hu.aestronglyMeasurable.star.comp_fst.mul hv.aestronglyMeasurable.comp_snd).mul
      hK.aestronglyMeasurable)
  filter_upwards [] with p
  simpa only [Pi.mul_apply, Pi.star_apply, norm_mul, norm_star] using
    mul_le_mul_of_nonneg_left (hC p) (mul_nonneg (norm_nonneg (u p.1)) (norm_nonneg (v p.2)))

lemma kernelDifference_measurePreserving :
    MeasurePreserving (fun p : ℝ × ℝ => (p.2 - p.1, p.2))
      (volume.prod volume) (volume.prod volume) := by
  have h := ((Measure.measurePreserving_neg (volume : Measure ℝ)).prod
    (MeasurePreserving.id (volume : Measure ℝ))).comp
      (measurePreserving_sub_prod (volume : Measure ℝ) (volume : Measure ℝ))
  simpa only [Function.comp_def, Prod.map_apply, id_eq, neg_sub] using h

lemma kernel_integral_change_variables (A : ℝ × ℝ → ℂ)
    (hA : Integrable A (volume.prod volume))
    (k : ℝ → ℂ) (hk : Continuous k) (C : ℝ) (hC : ∀ r, ‖k r‖ ≤ C) :
    (∫ r : ℝ, ∫ s : ℝ, k r * A (s - r, s)) =
      ∫ t : ℝ, ∫ s : ℝ, k (s - t) * A (t, s) := by
  have hi : Integrable (fun p : ℝ × ℝ => A (p.2 - p.1, p.2)) (volume.prod volume) :=
    (kernelDifference_measurePreserving.integrable_comp hA.aestronglyMeasurable).mpr hA
  have hi₁ : Integrable (fun p : ℝ × ℝ => k p.1 * A (p.2 - p.1, p.2))
      (volume.prod volume) := by
    apply (hi.norm.const_mul C).mono'
      ((hk.comp continuous_fst).aestronglyMeasurable.mul hi.aestronglyMeasurable)
    filter_upwards [] with p
    simpa only [Pi.mul_apply, Function.comp_def, norm_mul] using
      mul_le_mul_of_nonneg_right (hC p.1) (norm_nonneg (A (p.2 - p.1, p.2)))
  have hi₂ : Integrable (fun p : ℝ × ℝ => k (p.1 - p.2) * A (p.2, p.1))
      (volume.prod volume) := by
    apply (hA.swap.norm.const_mul C).mono'
      ((hk.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable.mul
        hA.swap.aestronglyMeasurable)
    filter_upwards [] with p
    simpa only [Pi.mul_apply, Function.comp_def, Pi.sub_apply, Prod.swap, norm_mul] using
      mul_le_mul_of_nonneg_right (hC (p.1 - p.2)) (norm_nonneg (A (p.2, p.1)))
  calc
    _ = ∫ s : ℝ, ∫ r : ℝ, k r * A (s - r, s) := integral_integral_swap hi₁
    _ = ∫ s : ℝ, ∫ t : ℝ, k (s - t) * A (t, s) := by
      apply integral_congr_ae
      filter_upwards [] with s
      simpa only [sub_sub_cancel] using
        (integral_sub_left_eq_self (fun r : ℝ => k r * A (s - r, s)) volume s).symm
    _ = _ := integral_integral_swap hi₂

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def scalarKernelMatrixCoefficient
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (f g : Lp ℂ 2 (volume : Measure ℝ)) (x y : H) (p : ℝ × ℝ) : ℂ :=
  inner ℂ (modularSliceKernel T f g p.2 p.1 x) y

lemma scalarKernelMatrixCoefficient_continuous
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (f g : Lp ℂ 2 (volume : Measure ℝ)) (x y : H) :
    Continuous (scalarKernelMatrixCoefficient T f g x y) := by
  have hp : Continuous (fun p : ℝ × ℝ => (p.2, p.1)) :=
    continuous_snd.prodMk continuous_fst
  have hc : Continuous (fun p : ℝ × ℝ => modularSliceKernel T f g p.2 p.1) := by
    change Continuous ((fun p : ℝ × ℝ => modularSliceKernel T f g p.1 p.2) ∘
      (fun p : ℝ × ℝ => (p.2, p.1)))
    exact (modularSliceKernel_continuous T f g).comp hp
  exact (hc.clm_apply continuous_const).inner continuous_const

lemma scalarKernelMatrixCoefficient_bound
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (f g : Lp ℂ 2 (volume : Measure ℝ)) (x y : H) (p : ℝ × ℝ) :
    ‖scalarKernelMatrixCoefficient T f g x y p‖ ≤
      (‖f‖ * ‖T‖ * ‖g‖ * ‖x‖) * ‖y‖ := by
  apply (norm_inner_le_norm _ _).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg y)
  exact ((modularSliceKernel T f g p.2 p.1).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (modularSliceKernel_norm_le T f g p.2 p.1) (norm_nonneg x))

end WeakPureInfiniteness

end

end OAI
