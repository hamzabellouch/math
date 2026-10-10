import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.CheegerHeat
import OAI.Geometry.WeakHessian.HeatFlow.RealHeatRangeError
import OAI.Geometry.WeakHessian.Sobolev.GlobalCheegerEnergyReal
import OAI.Geometry.WeakHessian.Sobolev.CompContDiff2
import OAI.Geometry.WeakHessian.Entropy.LocalGradientParallelogramCheeger

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open MeasureTheory Filter WeakHessianFunctional
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma sq_exp_eq (r : ℝ) : (Real.exp r)^2 = Real.exp (2*r) := by
  rw [pow_two,← Real.exp_add,two_mul]

lemma IsLaplacian.davies_form (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {u A : X → ℝ} (hu : IsLaplacian m u A)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V) {B : ℝ}
    (hB : ∀ᵐ x ∂m, V x ≤ B) :
    (∫ x, A x * u x * Real.exp (2*V x) ∂m) ≤
      (L:ℝ)^2 * (∫ x, (u x)^2 * Real.exp (2*V x) ∂m) := by
  have hV2 : LipschitzWith (‖(2:ℝ)‖₊*L) (fun x => 2*V x) := (lipschitzWith_smul (2:ℝ)).comp hV
  have hB2 : ∀ᵐ x ∂m, 2*V x ≤ 2*B := hB.mono (fun x hx => by linarith)
  have hv := hu.1.mul_exp hfinite hV2 hB2
  have huV := hu.1.mul_exp hfinite hV hB
  have hi : Integrable (fun x => (u x)^2*Real.exp (2*V x)) m := by
    apply huV.1.integrable_sq.congr
    exact ae_of_all _ (fun x => by simp only [mul_pow,sq_exp_eq])
  have hlap := hu.2.2 (fun x => u x*Real.exp (2*V x)) hv
  have hg : gamma m u (fun x => u x*Real.exp (2*V x)) =ᵐ[m]
      (fun x => Real.exp (2*V x)*((weakGradient m u x)^2+2*u x*gamma m V u x)) := by
    filter_upwards [gamma_comm (m := m) u (fun x => u x*Real.exp (2*V x)),
      gamma_mul_exp_left hfinite hpar hu.1.2.1 (localSobolev_of_lipschitz hfinite hV2)
        hu.1.2.1 hB2 (weakGradient_le_lipschitz hfinite hV2),
      gamma_self (m := m) u,
      gamma_const_mul_left hfinite hpar (localSobolev_of_lipschitz hfinite hV) hu.1.2.1 2]
      with x hc hm hs hc2
    rw [hc,hm,hs,hc2]
    ring
  have hb : ∀ᵐ x ∂m, -gamma m u (fun x => u x*Real.exp (2*V x)) x ≤
      (L:ℝ)^2*((u x)^2*Real.exp (2*V x)) := by
    filter_upwards [hg,abs_gamma_le hfinite hpar (localSobolev_of_lipschitz hfinite hV) hu.1.2.1,
      weakGradient_le_lipschitz hfinite hV,weakGradient_nonneg (m := m) u] with x hx hgam hLip hD
    have hgL : |gamma m V u x| ≤ (L:ℝ)*weakGradient m u x :=
      hgam.trans (mul_le_mul_of_nonneg_right hLip hD)
    have hm : |u x*gamma m V u x| ≤ |u x| *(L:ℝ)*weakGradient m u x := by
      rw [abs_mul,mul_assoc]
      exact mul_le_mul_of_nonneg_left hgL (abs_nonneg _)
    have hp : -((weakGradient m u x)^2+2*u x*gamma m V u x) ≤ (L:ℝ)^2*(u x)^2 := by
      have hlow := (abs_le.mp hm).1
      nlinarith [sq_nonneg (weakGradient m u x-(L:ℝ)*|u x|),sq_abs (u x)]
    rw [hx]
    have HH := mul_le_mul_of_nonneg_left hp (Real.exp_pos (2*V x)).le
    nlinarith [HH]
  calc
    (∫ x, A x*u x*Real.exp (2*V x) ∂m) =
        -(∫ x, gamma m u (fun y => u y*Real.exp (2*V y)) x ∂m) := by
      have he : (∫ x, A x*u x*Real.exp (2*V x) ∂m) =
          ∫ x, A x*(u x*Real.exp (2*V x)) ∂m := by
        apply integral_congr_ae
        exact ae_of_all _ (fun x => mul_assoc _ _ _)
      rw [he]
      linarith
    _ ≤ (L:ℝ)^2*(∫ x, (u x)^2*Real.exp (2*V x) ∂m) := by
      rw [← integral_neg,← integral_const_mul]
      exact integral_mono_ae (integrable_gamma hfinite hu.1 hv).neg (hi.const_mul _) hb

end WeakHessian

namespace WeakHessian
open MeasureTheory Set Filter WeakHessianFunctional
open scoped Topology InnerProductSpace

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

noncomputable def expMulLp {V : X → ℝ} (hV : AEStronglyMeasurable V m)
    {B : ℝ} (hB : ∀ᵐ x ∂m, V x ≤ B) : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m :=
  boundedMulLp (Real.continuous_exp.comp_aestronglyMeasurable hV)
    (hB.mono (fun x hx => by simpa only [abs_of_pos (Real.exp_pos _)] using Real.exp_le_exp.mpr hx))

lemma expMulLp_ae {V : X → ℝ} (hV : AEStronglyMeasurable V m)
    {B : ℝ} (hB : ∀ᵐ x ∂m, V x ≤ B) (u : Lp ℝ 2 m) :
    expMulLp hV hB u =ᵐ[m] (fun x => u x*Real.exp (V x)) := boundedMulLp_ae _ _ u

lemma expMulLp_inner {V : X → ℝ} (hV : AEStronglyMeasurable V m)
    {B : ℝ} (hB : ∀ᵐ x ∂m, V x ≤ B) (u v : Lp ℝ 2 m) :
    ⟪expMulLp hV hB u,expMulLp hV hB v⟫_ℝ = ∫ x, v x*u x*Real.exp (2*V x) ∂m := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [expMulLp_ae hV hB u,expMulLp_ae hV hB v] with x hx hy
  simp only [RCLike.inner_apply,conj_trivial,hx,hy,← sq_exp_eq]
  ring

lemma expMulLp_norm_sq {V : X → ℝ} (hV : AEStronglyMeasurable V m)
    {B : ℝ} (hB : ∀ᵐ x ∂m, V x ≤ B) (u : Lp ℝ 2 m) :
    ‖expMulLp hV hB u‖^2 = ∫ x, (u x)^2*Real.exp (2*V x) ∂m := by
  rw [← real_inner_self_eq_norm_sq,expMulLp_inner]
  simp only [pow_two]

variable [MetricSpace X] [BorelSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]

lemma CurvatureDimension.cheegerHeat_davies_generator {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfinite : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V) {B : ℝ}
    (hB : ∀ᵐ x ∂m, V x ≤ B) {t : ℝ} (ht : 0 ≤ t) :
    ‖expMulLp hV.continuous.aestronglyMeasurable hB (cheegerHeat h t u)‖^2 ≤
      ‖expMulLp hV.continuous.aestronglyMeasurable hB u‖^2*Real.exp (2*(L:ℝ)^2*t) := by
  let : IsLocallyFiniteMeasure m := ⟨fun x =>
    ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,hfinite _ Metric.isBounded_ball⟩⟩
  let T := expMulLp hV.continuous.aestronglyMeasurable hB
  let f : ℝ → ℝ := fun s => ‖T (cheegerHeat h s u)‖^2
  let f' : ℝ → ℝ := fun s => 2*⟪T (cheegerHeat h s u),T (cheegerHeat h s A)⟫_ℝ
  have hder (s : ℝ) (hs : 0 ≤ s) : HasDerivWithinAt f (f' s) (Ici s) s := by
    have HS := (cheeger_closedQuadraticEnergy h).heat_deriv_form_right m (cheeger_domain_dense h) hu hs
    change HasDerivWithinAt (fun r : ℝ => cheegerHeat h r u) (cheegerHeat h s A) (Ici s) s at HS
    exact (T.hasFDerivAt.comp_hasDerivWithinAt s HS).norm_sq
  have hbound (s : ℝ) (_hs : 0 ≤ s) : f' s ≤ 2*(L:ℝ)^2*f s := by
    have hG := hcd.global_isLaplacian_of_formGenerator hfinite o h (cheegerHeat h s u)
      (cheegerHeat h s A) ((cheeger_closedQuadraticEnergy h).formGenerator_heat m hu s)
    have HD := hG.davies_form hfinite (hcd.global_localGradientParallelogram hfinite o h) hV hB
    dsimp only [f',f,T]
    rw [expMulLp_inner,expMulLp_norm_sq]
    linarith
  have hcont : ContinuousOn f (Icc 0 t) := by
    have H := (cheeger_closedQuadraticEnergy h).heat_lipschitz_on_generator m hu
    change LipschitzOnWith _ (fun s : ℝ => cheegerHeat h s u) (Ici 0) at H
    exact (T.continuous.comp_continuousOn (H.continuousOn.mono Icc_subset_Ici_self)).norm.pow 2
  have H := le_gronwallBound_of_liminf_deriv_right_le (f' := f') (K := 2*(L:ℝ)^2) (ε := 0) hcont
    (fun s hs r hr => (hder s hs.1).liminf_right_slope_le hr)
    (show f 0 ≤ ‖T u‖^2 by simp [f,T,cheegerHeat_zero])
    (fun s hs => by simpa only [add_zero] using hbound s hs.1) t (show t ∈ Icc 0 t from ⟨ht,le_rfl⟩)
  simpa only [gronwallBound_ε0,sub_zero,f,T] using H

end WeakHessian

end
end InlinedFile0

end OAI
