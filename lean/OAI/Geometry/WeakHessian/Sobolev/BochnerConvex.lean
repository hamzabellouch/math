import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.SharpHeatGradient

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile99
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [ProperSpace X] [SigmaFinite m] in
lemma integrable_bounded_gamma (hfin : FiniteOnBoundedSets m) {u v e : X → ℝ}
    (hu : Sobolev m u) (hv : Sobolev m v) (he : AEStronglyMeasurable e m)
    {C : ℝ} (hC : ∀ᵐ x ∂m,|e x| ≤ C) : Integrable (fun x => e x*gamma m u v x) m := by
  apply (integrable_gamma hfin hu hv).bdd_mul he
  simpa only [Real.norm_eq_abs] using hC

omit [ProperSpace X] [SigmaFinite m] in
lemma weighted_gradient_tangent (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {u v e : X → ℝ} (hu : Sobolev m u) (hv : Sobolev m v)
    (he : AEStronglyMeasurable e m) (hen : ∀ᵐ x ∂m,0 ≤ e x)
    {C : ℝ} (hC : ∀ᵐ x ∂m,|e x| ≤ C) :
    2*(∫ x,e x*gamma m u v x ∂m)-(∫ x,e x*(weakGradient m u x)^2 ∂m) ≤
      ∫ x,e x*(weakGradient m v x)^2 ∂m := by
  have hiu := integrable_bounded_weakGradient_sq hu he hC
  have hiv := integrable_bounded_weakGradient_sq hv he hC
  have hig := integrable_bounded_gamma hfin hu hv he hC
  rw [← integral_const_mul,← integral_sub (hig.const_mul 2) hiu]
  apply integral_mono_ae ((hig.const_mul 2).sub hiu) hiv
  filter_upwards [abs_gamma_le hfin hpar hu.2.1 hv.2.1,hen] with x hx hn
  have hb : 2*gamma m u v x-(weakGradient m u x)^2 ≤ (weakGradient m v x)^2 := by
    have hh := (le_abs_self (gamma m u v x)).trans hx
    nlinarith [sq_nonneg (weakGradient m u x-weakGradient m v x)]
  change 2*(e x*gamma m u v x)-e x*(weakGradient m u x)^2 ≤ e x*(weakGradient m v x)^2
  nlinarith [mul_le_mul_of_nonneg_left hb hn]

omit [ProperSpace X] [SigmaFinite m] in
lemma IsLaplacian.weighted_pairing (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {u A v e : X → ℝ}
    (hu : IsLaplacian m u A) (hv : Sobolev m v)
    {L : ℝ≥0} (he : LipschitzWith L e) {C : ℝ} (hC : ∀ᵐ x ∂m,|e x| ≤ C) :
    (∫ x,e x*gamma m u v x ∂m) =
      -(∫ x,v x*(e x*A x+gamma m e u x) ∂m) := by
  have hes := localSobolev_of_lipschitz hfin he
  have heD : ∀ᵐ x ∂m,|weakGradient m e x| ≤ (L:ℝ) := by
    filter_upwards [weakGradient_le_lipschitz hfin he,weakGradient_nonneg (m := m) e] with x hx hn
    rwa [abs_of_nonneg hn]
  have hve := hv.mul_bounded hfin hes hC heD
  have hAu := memLp_mul_bounded hu.2.1 he.continuous.aestronglyMeasurable hC
  have hΓ := memLp_gamma_of_lipschitz hfin hpar he hu.1
  have h1 : Integrable (fun x => v x*gamma m e u x) m := hv.1.integrable_mul hΓ
  have h2 := integrable_bounded_gamma hfin hu.1 hv he.continuous.aestronglyMeasurable hC
  have h3 : Integrable (fun x => v x*(A x*e x)) m := hv.1.integrable_mul hAu
  have H := hu.2.2 (fun x => v x*e x) hve
  have heq : gamma m u (fun x => v x*e x) =ᵐ[m]
      (fun x => v x*gamma m e u x+e x*gamma m u v x) := by
    filter_upwards [gamma_comm (m := m) u (fun x => v x*e x),
      gamma_mul_left hfin hpar hv.2.1 hes hu.1.2.1 hC heD,gamma_comm (m := m) v u] with x hx hy hz
    rw [hx,hy,hz]
  rw [integral_congr_ae heq,integral_add h1 h2] at H
  have h3' : Integrable (fun x => v x*(e x*A x)) m := by simpa only [mul_comm (e _)] using h3
  rw [show (fun x => v x*(e x*A x+gamma m e u x)) =
      (fun x => v x*(e x*A x)+v x*gamma m e u x) by funext x; ring,
    integral_add h3' h1]
  have HE : (∫ x,A x*(v x*e x) ∂m) = ∫ x,v x*(e x*A x) ∂m := by congr 1; funext x; ring
  rw [HE] at H
  linarith

lemma right_deriv_nonneg_of_nonneg {f : ℝ → ℝ} {d : ℝ}
    (hf : HasDerivWithinAt f d (Ici 0) 0) (h0 : f 0 = 0)
    (hn : ∀ t,0 ≤ t → 0 ≤ f t) : 0 ≤ d := by
  have ht := (hasDerivWithinAt_iff_tendsto_slope' (show (0:ℝ) ∉ Ioi 0 by simp)).mp hf.Ioi_of_Ici
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [slope_def_field,h0,sub_zero]
  exact div_nonneg (hn t ht.le) ht.le
end WeakHessian

end
end InlinedFile99

end OAI
