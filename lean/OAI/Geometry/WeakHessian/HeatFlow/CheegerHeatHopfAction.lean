import Mathlib
import OAI.Geometry.WeakHessian.Transport.DerivEventuallyUpperRight
import OAI.Geometry.WeakHessian.Transport.BoundedHopfMapNorm
import OAI.Geometry.WeakHessian.HeatFlow.CheegerHeatBoundedPairing

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
open scoped Topology BoundedContinuousFunction NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma CurvatureDimension.cheegerHeat_hopf_action_interval {K N : ℝ} (hN : 1 < N)
    (hcd : CurvatureDimension m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hi : Integrable u m) (hA : Integrable A m)
    (f : X →ᵇ ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hI : ∀ᵐ t ∂volume.restrict (Icc a b), Integrable (fisherDensity (m := m) (cheegerHeat h t u)) m)
    (hIt : IntervalIntegrable (fun t => (∫ x,fisherDensity (m := m) (cheegerHeat h t u) x ∂m)/2) volume a b) :
    (∫ x,cheegerHeat h b u x*boundedHopfMap f b x ∂m)-
      (∫ x,cheegerHeat h a u x*boundedHopfMap f a x ∂m) ≤
      ∫ t in a..b,(∫ x,fisherDensity (m := m) (cheegerHeat h t u) x ∂m)/2 := by
  have hLip := hopf_L1_lipschitz f (fun s hs => (cheegerHeat_integrable hfin o h u hi hs).1)
    (integral_nonneg fun x => norm_nonneg (u x)) (integral_nonneg fun x => norm_nonneg (A x))
    (fun s hs => (cheegerHeat_integrable hfin o h u hi hs).2)
    (fun s t hs ht => hcd.cheegerHeat_L1_lipschitz hN hfull hfin o h hu hi hA hs ht) ha
  have hAC : AbsolutelyContinuousOnInterval (fun s => ∫ x,cheegerHeat h s u x*boundedHopfMap f s x ∂m) a b := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    exact hLip.mono (by rw [uIcc_of_le hab]; exact Icc_subset_Ici_self)
  apply sub_le_integral_of_upper_right_slope hab hAC hIt
  filter_upwards [hI,ae_restrict_mem measurableSet_Icc] with t ht hti
  exact fun r hr => hcd.cheegerHeat_hopf_upper_slope hN hfull hfin o h hu hun hi hA f (ha.trans_le hti.1) ht hr

lemma CurvatureDimension.cheegerHeat_hopf_continuousOn {K N : ℝ} (hN : 1 < N)
    (hcd : CurvatureDimension m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m) (hi : Integrable u m)
    {f : X →ᵇ ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    ContinuousOn (fun s => ∫ x,cheegerHeat h s u x*boundedHopfMap f s x ∂m) (Ici 0) := by
  intro t ht
  change 0 ≤ t at ht
  have hid : Tendsto (fun s : ℝ => s) (𝓝[Ici 0] t) (𝓝 t) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hs : Tendsto (fun s : ℝ => max s 0) (𝓝[Ici 0] t) (𝓝 t) := by
    simpa only [max_eq_left ht] using hid.max (tendsto_const_nhds (x := (0:ℝ)))
  have hL1 := hcd.cheegerHeat_L1_tendsto hN hfull hfin o h u hi (fun s : ℝ => le_max_right s 0) ht hs
  have hq := ((continuousOn_boundedHopfMap hf) t ht).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨hs,Eventually.of_forall fun s : ℝ => le_max_right s 0⟩)
  have H := tendsto_bounded_pairing_L1
    (fun s : ℝ => (cheegerHeat_integrable hfin o h u hi (le_max_right s 0)).1)
    (cheegerHeat_integrable hfin o h u hi ht).1 hq hL1
  apply H.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  change 0 ≤ s at hs
  simp only [Function.comp_apply,max_eq_left hs]

lemma CurvatureDimension.cheegerHeat_hopf_action {K N : ℝ} (hN : 1 < N)
    (hcd : CurvatureDimension m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hi : Integrable u m) (hA : Integrable A m)
    {f : X →ᵇ ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) {b : ℝ} (hb : 0 < b)
    (hI : ∀ᵐ t ∂volume.restrict (Icc 0 b), Integrable (fisherDensity (m := m) (cheegerHeat h t u)) m)
    (hIt : IntervalIntegrable (fun t => (∫ x,fisherDensity (m := m) (cheegerHeat h t u) x ∂m)/2) volume 0 b) :
    (∫ x,cheegerHeat h b u x*boundedHopfMap f b x ∂m)-(∫ x,u x*f x ∂m) ≤
      ∫ t in 0..b,(∫ x,fisherDensity (m := m) (cheegerHeat h t u) x ∂m)/2 := by
  let I (t : ℝ) := (∫ x,fisherDensity (m := m) (cheegerHeat h t u) x ∂m)/2
  let J (t : ℝ) := ∫ x,cheegerHeat h t u x*boundedHopfMap f t x ∂m
  have hIn : 0 ≤ᵐ[volume.restrict (Ioc 0 b)] I := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    apply div_nonneg _ (by norm_num)
    apply integral_nonneg_of_ae
    filter_upwards [cheegerHeat_nonneg h ht.1.le u hun] with x hx
    exact div_nonneg (sq_nonneg _) hx
  have hbound (a : ℝ) (ha : 0 < a) (hab : a ≤ b) : J b-J a ≤ ∫ t in 0..b,I t := by
    have hsub : Icc a b ⊆ Icc 0 b := Icc_subset_Icc ha.le le_rfl
    have hIa := hI.filter_mono (MeasureTheory.ae_mono (Measure.restrict_mono hsub le_rfl))
    have hIta := hIt.mono_set (by rwa [uIcc_of_le hab,uIcc_of_le hb.le])
    have H := hcd.cheegerHeat_hopf_action_interval hN hfull hfin o h hu hun hi hA f ha hab hIa hIta
    exact H.trans (intervalIntegral.integral_mono_interval ha.le hab le_rfl hIn hIt)
  have hc := hcd.cheegerHeat_hopf_continuousOn hN hfull hfin o h u hi hf
  have hlim : Tendsto J (𝓝[>] 0) (𝓝 (J 0)) :=
    (hc 0 (show (0:ℝ) ∈ Ici 0 from (show (0:ℝ) ≤ 0 from le_rfl))).tendsto.mono_left
      (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have H : J b-J 0 ≤ ∫ t in 0..b,I t := by
    apply le_of_tendsto (tendsto_const_nhds.sub hlim)
    filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with a ha hab
    exact hbound a ha hab.le
  simpa only [J,I,cheegerHeat_zero,one_apply_eq_self,boundedHopfMap_zero] using H
end WeakHessian
end

end OAI
