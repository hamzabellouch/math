import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.CappedTransformAdjoint
import OAI.Analysis.RieszRectifiability.Kernel.CappedMeanZeroTail

namespace OAI

/-!
# Renormalized exterior adjoints

Mean-zero cancellation removes the constant kernel term from the capped
transform. The far-kernel difference is integrable against bounded densities
and integrable compactly supported tests, so Fubini and kernel antisymmetry give
the exterior adjoint identity with its minus sign.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Filter Set

theorem mean_zero_centered_capped_integral {d : ℕ} (m : ℕ)
    (ν : Measure (Ambient d)) (e : Ambient d) (ε : ℝ) (hε : 0 < ε)
    (g : Ambient d → ℝ) (hgm : Measurable g) (hg : Integrable g ν)
    (hmean : (∫ x, g x ∂ν) = 0) (y : Ambient d) (c : ℝ) :
    (∫ x, g x * (scalarCappedRieszKernel m e ε (y, x) - c) ∂ν) =
      scalarCappedTransform m ν e ε g y := by
  have hi := (scalarCappedTransform_integrable_and_bound m ν e ε hε g hgm hg y).1
  simp only [mul_sub]
  rw [integral_sub hi (hg.mul_const c), integral_mul_const, hmean, zero_mul, sub_zero]
  rfl

theorem density_renormalized_cross_product_integrable {d : ℕ} (m : ℕ) (C : ℝ)
    (μ ν : Measure (Ambient d)) [SFinite μ] [SFinite ν] (hμ : GlobalUpperGrowth m C μ)
    (e a : Ambient d) (H R : ℝ) (hH : 0 < H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (f g : Ambient d → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (M : ℝ) (hfb : ∀ y, |f y| ≤ M) (hg : Integrable g ν)
    (hgs : ∀ x, g x ≠ 0 → dist x a ≤ H) :
    Integrable (fun q : Ambient d × Ambient d =>
      f q.2 * g q.1 * inner ℝ e (kernel m q.1 q.2 - kernel m a q.2))
      (ν.prod (μ.restrict (closedExterior a R))) := by
  let E := closedExterior a R
  let A := (2 ^ (m + 1) + (m + 1 : ℝ) * 2 ^ (m + 2)) * (‖e‖ * H)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hM : 0 ≤ M := (abs_nonneg (f 0)).trans (hfb 0)
  have hk := (inverseDistancePow_closedExterior_integrable_and_bound m C μ hμ a R hR).1
  have hmeas : Measurable (fun q : Ambient d × Ambient d =>
      f q.2 * g q.1 * inner ℝ e (kernel m q.1 q.2 - kernel m a q.2)) := by
    let : ContinuousSMul ℝ (Ambient d) := IsBoundedSMul.continuousSMul
    unfold kernel
    fun_prop
  apply ((hg.abs.mul_prod hk).const_mul (M * A)).mono' hmeas.aestronglyMeasurable
  have hE : MeasurableSet E := closedExterior_measurable a R
  have hmem : ∀ᵐ q ∂ν.prod (μ.restrict E), q.2 ∈ E :=
    (Measure.ae_prod_iff_ae_ae (hE.preimage measurable_snd)).mpr
      (Eventually.of_forall fun _ => ae_restrict_mem hE)
  filter_upwards [hmem] with q hq
  by_cases hx : g q.1 = 0
  · simp only [hx, mul_zero, zero_mul, norm_zero, abs_zero, le_refl]
  have hinner : |inner ℝ e (kernel m q.1 q.2 - kernel m a q.2)| ≤
      A * inverseDistancePow (m + 1) a q.2 := by
    apply (scalar_far_kernel_bound m e a q.1 q.2 R hR
      ((mul_le_mul_of_nonneg_left (hgs q.1 hx) (by norm_num)).trans hHR) hq).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hgs q.1 hx) (norm_nonneg _))
        (by positivity)) (inverseDistancePow_nonneg _ _ _)
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  calc
    _ ≤ (M * |g q.1|) * (A * inverseDistancePow (m + 1) a q.2) :=
      mul_le_mul (mul_le_mul_of_nonneg_right (hfb q.2) (abs_nonneg _)) hinner
        (abs_nonneg _) (mul_nonneg hM (abs_nonneg _))
    _ = _ := by ring

theorem density_renormalized_exterior_adjoint {d : ℕ} (m : ℕ) (C : ℝ)
    (μ ν : Measure (Ambient d)) [SFinite μ] [SFinite ν] (hμ : GlobalUpperGrowth m C μ)
    (e a : Ambient d) (H R ε : ℝ) (hH : 0 < H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hε : 0 < ε) (hεH : ε ≤ H)
    (f g : Ambient d → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (M : ℝ) (hfb : ∀ y, |f y| ≤ M) (hg : Integrable g ν)
    (hmean : (∫ x, g x ∂ν) = 0) (hgs : ∀ x, g x ≠ 0 → dist x a ≤ H) :
    Integrable (fun x => (∫ y in closedExterior a R,
      f y * inner ℝ e (kernel m x y - kernel m a y) ∂μ) * g x) ν ∧
      IntegrableOn (fun y => f y * scalarCappedTransform m ν e ε g y) (closedExterior a R) μ ∧
      (∫ x, (∫ y in closedExterior a R,
        f y * inner ℝ e (kernel m x y - kernel m a y) ∂μ) * g x ∂ν) =
        -(∫ y in closedExterior a R, f y * scalarCappedTransform m ν e ε g y ∂μ) := by
  let E := closedExterior a R
  let F : Ambient d × Ambient d → ℝ := fun q =>
    f q.2 * g q.1 * inner ℝ e (kernel m q.1 q.2 - kernel m a q.2)
  have hF : Integrable F (ν.prod (μ.restrict E)) :=
    density_renormalized_cross_product_integrable m C μ ν hμ e a H R hH hR hHR f g hfm hgm M hfb hg hgs
  have hleft (x : Ambient d) : (∫ y in E, F (x, y) ∂μ) =
      (∫ y in E, f y * inner ℝ e (kernel m x y - kernel m a y) ∂μ) * g x := by
    calc
      _ = ∫ y in E, (f y * inner ℝ e (kernel m x y - kernel m a y)) * g x ∂μ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun y => by dsimp only [F]; ring
      _ = _ := integral_mul_const _ _
  have hright : (fun y => ∫ x, F (x, y) ∂ν) =ᵐ[μ.restrict E]
      (fun y => -(f y * scalarCappedTransform m ν e ε g y)) := by
    filter_upwards [ae_restrict_mem (closedExterior_measurable a R)] with y hy
    have hya : ε ≤ dist y a := by
      have hy' : R ≤ dist a y := hy
      rw [dist_comm y a]
      linarith
    calc
      _ = ∫ x, -(f y * (g x * (scalarCappedRieszKernel m e ε (y, x) -
          scalarCappedRieszKernel m e ε (y, a)))) ∂ν := by
        apply integral_congr_ae
        apply Eventually.of_forall
        intro x
        dsimp only [F]
        by_cases hx : g x = 0
        · simp only [hx, mul_zero, zero_mul, neg_zero]
        have hyx : ε ≤ dist y x := by
          have ht := dist_triangle a x y
          rw [dist_comm a x, dist_comm x y] at ht
          have hxH := hgs x hx
          have hyR : R ≤ dist a y := hy
          linarith
        rw [scalarCappedRieszKernel, scalarCappedRieszKernel,
          cappedRieszKernel_eq_kernel m ε (y, x) hyx,
          cappedRieszKernel_eq_kernel m ε (y, a) hya,
          kernel_antisymm m x y, kernel_antisymm m a y]
        simp only [inner_neg_right, inner_sub_right]
        ring
      _ = -(f y * scalarCappedTransform m ν e ε g y) := by
        rw [integral_neg, integral_const_mul,
          mean_zero_centered_capped_integral m ν e ε hε g hgm hg hmean]
  have hLI := hF.integral_prod_left.congr (Eventually.of_forall hleft)
  have hRIneg := hF.integral_prod_right.congr hright
  have hRI : IntegrableOn (fun y => f y * scalarCappedTransform m ν e ε g y) E μ := by
    have hd : IntegrableOn (fun y => -(-(f y * scalarCappedTransform m ν e ε g y))) E μ := hRIneg.neg
    simpa only [neg_neg] using! hd
  refine ⟨hLI, hRI, ?_⟩
  calc
    _ = ∫ q, F q ∂ν.prod (μ.restrict E) :=
      ((integral_prod F hF).trans (integral_congr_ae (Eventually.of_forall hleft))).symm
    _ = ∫ y in E, -(f y * scalarCappedTransform m ν e ε g y) ∂μ :=
      (integral_prod_symm F hF).trans (integral_congr_ae hright)
    _ = _ := integral_neg _

end

end RieszRectifiability

end OAI
