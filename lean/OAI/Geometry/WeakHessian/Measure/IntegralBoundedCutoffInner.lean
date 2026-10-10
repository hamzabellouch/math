import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.CheegerHeatAbs

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
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Set Filter WeakHessianFunctional
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma integral_bounded_cutoff_eq_inner (hfin : FiniteOnBoundedSets m) (o : X)
    {φ : X → ℝ} (hφ : AEStronglyMeasurable φ m) {B : ℝ} (hB : ∀ᵐ x ∂m,‖φ x‖ ≤ B)
    (n : ℕ) (u : Lp ℝ 2 m) :
    (∫ x,u x*φ x*radialCutoff o n x ∂m) =
      ⟪boundedMulLp hφ hB (radialCutoffLp hfin o n),u⟫_ℝ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [boundedMulLp_ae hφ hB (radialCutoffLp hfin o n),radialCutoffLp_ae hfin o n] with x hx hc
  simp only [hx,hc,RCLike.inner_apply,conj_trivial]
  ring

lemma CurvatureDimension.cheegerHeat_bounded_FTC {K N : ℝ} (_ : 1 < N)
    (_ : CurvatureDimension m K N) (_ : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    (hi : Integrable u m) (hA : Integrable A m)
    {φ : X → ℝ} (hφ : AEStronglyMeasurable φ m) {B : ℝ}
    (hB : ∀ᵐ x ∂m, ‖φ x‖ ≤ B) {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in 0..t, ∫ x,cheegerHeat h s A x*φ x ∂m) =
      (∫ x,cheegerHeat h t u x*φ x ∂m)-(∫ x,u x*φ x ∂m) := by
  let fn : ℕ → ℝ → ℝ := fun n s => ∫ x,cheegerHeat h s A x*φ x*radialCutoff o n x ∂m
  have hcont (n : ℕ) : ContinuousOn (fn n) (Ici 0) := by
    have he : fn n = fun s => (innerSL ℝ (boundedMulLp hφ hB (radialCutoffLp hfin o n))) (cheegerHeat h s A) := by
      funext s; exact integral_bounded_cutoff_eq_inner hfin o hφ hB n _
    rw [he]
    exact (innerSL ℝ _).continuous.comp_continuousOn (cheegerHeat_continuousOn hfin h A)
  have hB' : ∀ᵐ x ∂m, ‖φ x‖ ≤ |B| := hB.mono fun x hx => hx.trans (le_abs_self _)
  have hb (n : ℕ) (s : ℝ) (hs : 0 ≤ s) : ‖fn n s‖ ≤ |B| *(∫ x,‖A x‖ ∂m) := by
    have hφχ := hφ.mul (radialCutoff_lipschitz o n).continuous.aestronglyMeasurable
    have hφχB : ∀ᵐ x ∂m, ‖φ x*radialCutoff o n x‖ ≤ |B| := by
      filter_upwards [hB'] with x hx
      rw [norm_mul,Real.norm_of_nonneg (radialCutoff_nonneg o n x)]
      exact (mul_le_mul hx (radialCutoff_le_one o n x) (radialCutoff_nonneg o n x) (abs_nonneg _)).trans_eq (mul_one _)
    simpa only [fn,mul_assoc,Pi.mul_apply] using cheegerHeat_pairing_bound hfin o h A hA hφχ hφχB hs
  have hlim (s : ℝ) (hs : 0 ≤ s) : Tendsto (fun n => fn n s) atTop
      (𝓝 (∫ x,cheegerHeat h s A x*φ x ∂m)) :=
    integral_radialCutoff_tendsto o ((cheegerHeat_integrable hfin o h A hA hs).1.mul_bdd hφ hB)
  have htime : Tendsto (fun n => ∫ s in 0..t,fn n s) atTop
      (𝓝 (∫ s in 0..t,∫ x,cheegerHeat h s A x*φ x ∂m)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => |B| *(∫ x,‖A x‖ ∂m))
    · exact Eventually.of_forall fun n => ((hcont n).mono
        (show uIoc (0:ℝ) t ⊆ Ici 0 by rw [uIoc_of_le ht]; exact fun _ hx => hx.1.le)).aestronglyMeasurable measurableSet_uIoc
    · exact Eventually.of_forall fun n => ae_of_all _ fun s hs => hb n s (by rw [uIoc_of_le ht] at hs; exact hs.1.le)
    · exact intervalIntegrable_const
    · exact ae_of_all _ fun s hs => hlim s (by rw [uIoc_of_le ht] at hs; exact hs.1.le)
  have hFTC (n : ℕ) : (∫ s in 0..t,fn n s) =
      (∫ x,cheegerHeat h t u x*φ x*radialCutoff o n x ∂m)-(∫ x,u x*φ x*radialCutoff o n x ∂m) := by
    let T := innerSL ℝ (boundedMulLp hφ hB (radialCutoffLp hfin o n))
    have hAint : IntervalIntegrable (fun s => cheegerHeat h s A) volume 0 t :=
      ((cheegerHeat_continuousOn hfin h A).mono (show uIcc (0:ℝ) t ⊆ Ici 0 by
        rw [uIcc_of_le ht]; exact Icc_subset_Ici_self)).intervalIntegrable
    have H := congrArg T (cheegerHeat_integral_generator hfin h hu ht)
    rw [← T.intervalIntegral_comp_comm hAint,map_sub] at H
    simpa only [T,innerSL_apply_apply,← integral_bounded_cutoff_eq_inner hfin o hφ hB n,fn] using H
  have hs := (integral_radialCutoff_tendsto o ((cheegerHeat_integrable hfin o h u hi ht).1.mul_bdd hφ hB)).sub
    (integral_radialCutoff_tendsto o (hi.mul_bdd hφ hB))
  simp_rw [hFTC] at htime
  exact tendsto_nhds_unique htime hs

lemma CurvatureDimension.cheegerHeat_bounded_deriv_right {K N : ℝ} (hN : 1 < N)
    (hcd : CurvatureDimension m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    (hi : Integrable u m) (hA : Integrable A m)
    {φ : X → ℝ} (hφ : AEStronglyMeasurable φ m) {B : ℝ}
    (hB : ∀ᵐ x ∂m, ‖φ x‖ ≤ B) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => ∫ x,cheegerHeat h s u x*φ x ∂m)
      (∫ x,cheegerHeat h t A x*φ x ∂m) (Ici t) t := by
  let g (s : ℝ) := ∫ x,cheegerHeat h (max s 0) A x*φ x ∂m
  have hc : Continuous g := (hcd.cheegerHeat_bounded_pairing_continuousOn hN hfull hfin o h A hA hφ hB).comp_continuous
    (continuous_id.max continuous_const) (fun s => le_max_right s 0)
  have he (r : ℝ) (hr : 0 ≤ r) : (∫ s in 0..r,g s) =
      (∫ x,cheegerHeat h r u x*φ x ∂m)-(∫ x,u x*φ x ∂m) := by
    rw [← hcd.cheegerHeat_bounded_FTC hN hfull hfin o h hu hi hA hφ hB hr]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hr] at hs
    simp only [g,max_eq_left hs.1]
  have hd := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt).add_const (∫ x,u x*φ x ∂m)
  have H : HasDerivWithinAt (fun r => (∫ s in 0..r,g s)+(∫ x,u x*φ x ∂m))
      (∫ x,cheegerHeat h t A x*φ x ∂m) (Ici t) t := by
    simpa only [g,max_eq_left ht] using hd.hasDerivWithinAt (s := Ici t)
  apply H.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with r hr
    rw [he r (ht.trans hr)]
    ring
  · rw [he t ht]; ring
end WeakHessian

end
end InlinedFile0

end OAI
