import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.SharpHeatGradient

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile102
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [ProperSpace X] [SigmaFinite m] in
lemma weighted_gradient_loss (hfin : FiniteOnBoundedSets m)
    {u v E : Lp ℝ 2 m} (hu : Sobolev m (u : X → ℝ)) (hv : Sobolev m (v : X → ℝ))
    (hE : IsLocalWeakUpperGradient m (v-u : Lp ℝ 2 m) E)
    {e : X → ℝ} (he : AEStronglyMeasurable e m) (hen : ∀ᵐ x ∂m,0 ≤ e x)
    {B : ℝ} (hB : 0 ≤ B) (heb : ∀ᵐ x ∂m,|e x| ≤ B) :
    (∫ x,e x*(weakGradient m (u : X → ℝ) x)^2 ∂m)-
      (∫ x,e x*(weakGradient m (v : X → ℝ) x)^2 ∂m) ≤
      B*‖E‖*(‖hu.2.2.toLp (weakGradient m (u : X → ℝ))‖+
        ‖hv.2.2.toLp (weakGradient m (v : X → ℝ))‖) := by
  let D := hu.2.2.toLp (weakGradient m (u : X → ℝ))
  let W := hv.2.2.toLp (weakGradient m (v : X → ℝ))
  have hdiff := hE.congr_ae (Lp.coeFn_sub v u) .rfl
  have hmin := (weakGradient_isMinimal (hv.2.1.sub hfin hu.2.1).2).2 E hdiff
  have hi := (Lp.memLp E).integrable_mul (hu.2.2.add hv.2.2)
  have HH : (∫ x,e x*(weakGradient m (u : X → ℝ) x)^2 ∂m)-
      (∫ x,e x*(weakGradient m (v : X → ℝ) x)^2 ∂m) ≤
      B*(∫ x,E x*(weakGradient m (u : X → ℝ) x+weakGradient m (v : X → ℝ) x) ∂m) := by
    rw [← integral_sub (integrable_bounded_weakGradient_sq hu he heb)
      (integrable_bounded_weakGradient_sq hv he heb),← integral_const_mul]
    apply integral_mono_ae
      ((integrable_bounded_weakGradient_sq hu he heb).sub (integrable_bounded_weakGradient_sq hv he heb)) (hi.const_mul B)
    filter_upwards [weakGradient_dist_le hfin hv.2.1 hu.2.1,hmin,weakGradient_nonneg (m := m) (u : X → ℝ),
      weakGradient_nonneg (m := m) (v : X → ℝ),hE.2.1,hen,heb] with x hx hm hn1 hn2 hn3 hn4 hb
    have hd : weakGradient m (u : X → ℝ) x-weakGradient m (v : X → ℝ) x ≤ E x := by
      rw [abs_sub_comm] at hx
      exact (le_abs_self _).trans (hx.trans hm)
    have hs : (weakGradient m (u : X → ℝ) x)^2-(weakGradient m (v : X → ℝ) x)^2 ≤
        E x*(weakGradient m (u : X → ℝ) x+weakGradient m (v : X → ℝ) x) := by
      nlinarith [mul_le_mul_of_nonneg_right hd (add_nonneg hn1 hn2)]
    have hm1 := mul_le_mul_of_nonneg_left hs hn4
    have hm2 := mul_le_mul_of_nonneg_right ((le_abs_self (e x)).trans hb) (mul_nonneg hn3 (add_nonneg hn1 hn2))
    dsimp only [Pi.sub_apply,Pi.mul_apply,Pi.add_apply]
    nlinarith
  have hp : (∫ x,E x*(weakGradient m (u : X → ℝ) x+weakGradient m (v : X → ℝ) x) ∂m) = ⟪D+W,E⟫_ℝ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add D W,hu.2.2.coeFn_toLp,hv.2.2.coeFn_toLp] with x hx hd hw
    simp only [RCLike.inner_apply,conj_trivial,hx,Pi.add_apply,D,W,hd,hw]
  rw [hp] at HH
  calc
    _ ≤ B*⟪D+W,E⟫_ℝ := HH
    _ ≤ B*(‖D+W‖*‖E‖) := mul_le_mul_of_nonneg_left (real_inner_le_norm _ _) hB
    _ ≤ B*((‖D‖+‖W‖)*‖E‖) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (norm_add_le _ _) (norm_nonneg E)) hB
    _ = _ := by ring

omit [CompleteSpace X] [SigmaFinite m] in
lemma CurvatureDimension.cheegerHeat_minimal_norm {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m) (h : QuadraticCheegerEnergy m) (o : X)
    {u : Lp ℝ 2 m} (hu : Sobolev m (u : X → ℝ)) {t : ℝ} (ht : 0 ≤ t)
    (hv : Sobolev m (cheegerHeat h t u : X → ℝ)) :
    ‖hv.2.2.toLp (weakGradient m (cheegerHeat h t u : X → ℝ))‖ ≤
      ‖hu.2.2.toLp (weakGradient m (u : X → ℝ))‖ := by
  have H := cheegerHeat_energy_le h ht u
  rw [hcd.global_cheegerEnergy_eq_weakGradient hfin o hu,
    hcd.global_cheegerEnergy_eq_weakGradient hfin o hv] at H
  have H' := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp H
  nlinarith [norm_nonneg (hv.2.2.toLp (weakGradient m (cheegerHeat h t u : X → ℝ))),
    norm_nonneg (hu.2.2.toLp (weakGradient m (u : X → ℝ)))]
end WeakHessian

end
end InlinedFile102

end OAI
