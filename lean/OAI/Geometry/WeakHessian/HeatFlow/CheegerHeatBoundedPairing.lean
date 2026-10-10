import Mathlib
import OAI.Geometry.WeakHessian.Measure.IntegralBoundedCutoffInner
import OAI.Geometry.WeakHessian.Transport.BoundedHopfMapLipschitz

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

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
open WeakHessianTransport WeakHessianFunctional MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma CurvatureDimension.cheegerHeat_bounded_pairing_lipschitz {K N : ℝ} (hN : 1 < N)
    (hcd : CurvatureDimension m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    (hi : Integrable u m) (hA : Integrable A m)
    {φ : X → ℝ} (hφ : AEStronglyMeasurable φ m) {B : ℝ}
    (hB : ∀ᵐ x ∂m,‖φ x‖ ≤ B) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ‖(∫ x,cheegerHeat h t u x*φ x ∂m)-(∫ x,cheegerHeat h s u x*φ x ∂m)‖ ≤
      B*(∫ x,‖A x‖ ∂m)*(t-s) := by
  have hc := hcd.cheegerHeat_bounded_pairing_continuousOn hN hfull hfin o h u hi hφ hB
  have hcA := hcd.cheegerHeat_bounded_pairing_continuousOn hN hfull hfin o h A hA hφ hB
  have hsI : Icc s t ⊆ Ici 0 := fun x hx => hs.trans hx.1
  have hAI : IntervalIntegrable (fun r => ∫ x,cheegerHeat h r A x*φ x ∂m) volume s t := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hst]
    exact hcA.mono hsI
  have H := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hst (hc.mono hsI)
    (fun r hr => (hcd.cheegerHeat_bounded_deriv_right hN hfull hfin o h hu hi hA hφ hB
      (hs.trans hr.1.le)).Ioi_of_Ici) hAI
  rw [← H]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := t)
    (f := fun r => ∫ x,cheegerHeat h r A x*φ x ∂m) (C := B*(∫ x,‖A x‖ ∂m)) (by
      intro r hr
      rw [uIoc_of_le hst] at hr
      exact cheegerHeat_pairing_bound hfin o h A hA hφ hB (hs.trans hr.1.le))
  simpa only [abs_of_nonneg (sub_nonneg.mpr hst)] using hb

lemma CurvatureDimension.cheegerHeat_L1_lipschitz {K N : ℝ} (hN : 1 < N)
    (hcd : CurvatureDimension m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    (hi : Integrable u m) (hA : Integrable A m) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (∫ x,‖cheegerHeat h t u x-cheegerHeat h s u x‖ ∂m) ≤
      (∫ x,‖A x‖ ∂m)*|t-s| := by
  have H (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
      (∫ x,‖cheegerHeat h t u x-cheegerHeat h s u x‖ ∂m) ≤
        (∫ x,‖A x‖ ∂m)*(t-s) := by
    let φ (x : X) := if 0 ≤ cheegerHeat h t u x-cheegerHeat h s u x then (1:ℝ) else -1
    have hφ : AEStronglyMeasurable φ m := by
      have hm : MeasurableSet {x | 0 ≤ cheegerHeat h t u x-cheegerHeat h s u x} :=
        measurableSet_le measurable_const ((Lp.stronglyMeasurable _).measurable.sub (Lp.stronglyMeasurable _).measurable)
      exact (Measurable.ite hm measurable_const measurable_const).aestronglyMeasurable
    have hB : ∀ x,‖φ x‖ ≤ 1 := by intro x; dsimp [φ]; split_ifs <;> norm_num
    have he : (∫ x,cheegerHeat h t u x*φ x ∂m)-(∫ x,cheegerHeat h s u x*φ x ∂m) =
        ∫ x,‖cheegerHeat h t u x-cheegerHeat h s u x‖ ∂m := by
      rw [← integral_sub ((cheegerHeat_integrable hfin o h u hi (hs.trans hst)).1.mul_bdd hφ (ae_of_all _ hB))
        ((cheegerHeat_integrable hfin o h u hi hs).1.mul_bdd hφ (ae_of_all _ hB))]
      apply integral_congr_ae
      apply ae_of_all
      intro x
      dsimp only
      rw [← sub_mul,Real.norm_eq_abs]
      dsimp only [φ]
      split_ifs with hx
      · rw [mul_one,abs_of_nonneg hx]
      · rw [mul_neg_one,abs_of_neg (lt_of_not_ge hx)]
    have hb := hcd.cheegerHeat_bounded_pairing_lipschitz hN hfull hfin o h hu hi hA hφ (ae_of_all _ hB) hs hst
    rw [he,Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg _),one_mul] at hb
    exact hb
  rcases le_total s t with hst|hts
  · simpa only [abs_of_nonneg (sub_nonneg.mpr hst)] using H s t hs hst
  · have hb := H t s ht hts
    simp_rw [norm_sub_rev (cheegerHeat h s u _) (cheegerHeat h t u _)] at hb
    simpa only [abs_of_nonpos (sub_nonpos.mpr hts),neg_sub] using hb

lemma CurvatureDimension.cheegerHeat_hopf_upper_slope {K N : ℝ} (hN : 1 < N)
    (hcd : CurvatureDimension m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hi : Integrable u m) (hA : Integrable A m)
    (f : X →ᵇ ℝ) {t : ℝ} (ht : 0 < t)
    (hI : Integrable (fisherDensity (m := m) (cheegerHeat h t u)) m)
    {r : ℝ} (hr : (∫ x,fisherDensity (m := m) (cheegerHeat h t u) x ∂m)/2 < r) :
    ∀ᶠ s in 𝓝[>] t,
      slope (fun z => ∫ x,cheegerHeat h z u x*boundedHopfMap f z x ∂m) t s < r := by
  have hL1 : Tendsto (fun s => ∫ x,‖cheegerHeat h s u x-cheegerHeat h t u x‖ ∂m)
      (𝓝[>] t) (𝓝 0) := by
    have hid : Tendsto (fun s : ℝ => s) (𝓝[>] t) (𝓝 t) := tendsto_id.mono_left nhdsWithin_le_nhds
    have hs : Tendsto (fun s : ℝ => max s 0) (𝓝[>] t) (𝓝 t) := by
      simpa only [max_eq_left ht.le] using hid.max (tendsto_const_nhds (x := (0:ℝ)))
    have H := hcd.cheegerHeat_L1_tendsto hN hfull hfin o h u hi
      (fun s : ℝ => le_max_right s 0) ht.le hs
    apply H.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [max_eq_left (ht.le.trans (le_of_lt hs))]
  obtain ⟨L,hLip⟩ := boundedHopfMap_lipschitz f ht
  have hB : ∀ x, |boundedHopfMap f t x| ≤ ‖boundedHopfMap f t‖ :=
    fun x => (boundedHopfMap f t).norm_coe_le_norm x
  have hd := hcd.cheegerHeat_bounded_deriv_right hN hfull hfin o h hu hi hA
    (boundedHopfMap f t).continuous.aestronglyMeasurable (ae_of_all _ hB) ht.le
  have hLap := hcd.global_isLaplacian_of_formGenerator hfin o h (cheegerHeat h t u)
    (cheegerHeat h t A) ((cheeger_closedQuadraticEnergy h).formGenerator_heat m hu t)
  have hpair := hLap.fisher_pairing hfin o (hcd.global_localGradientParallelogram hfin o h)
    (Lp.stronglyMeasurable _).measurable (cheegerHeat_nonneg h ht.le u hun)
    (cheegerHeat_integrable hfin o h u hi ht.le).1 hI
    (cheegerHeat_integrable hfin o h A hA ht.le).1 hLip hB
  exact hopf_L1_upper_slope hfin f (fun s hs => (cheegerHeat_integrable hfin o h u hi hs).1)
    ht (cheegerHeat_nonneg h ht.le u hun) hL1 hd (hpair.trans_lt hr)
end WeakHessian
end

end OAI
