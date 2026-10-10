import Mathlib
import OAI.Geometry.WeakHessian.Transport.CouplingCostBound

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace WeakHessian
open Set Filter MeasureTheory
open scoped ENNReal Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]

lemma CurvatureDimension.lift_bounded_coupling {m : Measure X} {K N : ℝ}
    (hcd : CurvatureDimension m K N) (q : Measure (X×X)) [IsFiniteMeasure q]
    (hac0 : q.map Prod.fst ≪ m) (hac1 : q.map Prod.snd ≪ m)
    (o : X) (R : ℝ) (hR : ∀ᵐ p ∂q, dist p.1 o ≤ R ∧ dist p.2 o ≤ R) :
    ∃ π : Measure (Curve X), interpolation π timeZero = q.map Prod.fst ∧
      interpolation π timeOne = q.map Prod.snd ∧
      (∫⁻ γ,kineticAction γ ∂π) ≤ QuadraticTransportCost q := by
  by_cases hq : q = 0
  · subst q
    exact ⟨0,by simp [interpolation],by simp [interpolation],by simp [QuadraticTransportCost]⟩
  have hz : q univ ≠ 0 := by intro H; exact hq (Measure.ext fun s hs => by have := measure_mono (subset_univ s) (μ := q); simp only [H,nonpos_iff_eq_zero] at this; simpa using this)
  have ht : q univ ≠ ∞ := measure_ne_top _ _
  let q' : Measure (X×X) := (q univ)⁻¹ • q
  have hp : IsProbabilityMeasure q' := by
    constructor
    simp only [q',Measure.smul_apply,smul_eq_mul,ENNReal.inv_mul_cancel hz ht]
  let := hp
  have hcancel : q univ • q' = q := by
    dsimp only [q']
    rw [smul_smul,ENNReal.mul_inv_cancel hz ht,one_smul]
  have hp0 : IsProbabilityMeasure (q'.map Prod.fst) := inferInstance
  have hp1 : IsProbabilityMeasure (q'.map Prod.snd) := inferInstance
  let := hp0
  let := hp1
  have hr : ∀ᵐ p ∂q', dist p.1 o ≤ R ∧ dist p.2 o ≤ R :=
    (Measure.AbsolutelyContinuous.rfl.smul_left _).ae_le hR
  have hmom (f : X×X → X) (hf : Measurable f) (hb : ∀ᵐ p ∂q',dist (f p) o ≤ R) :
      HasSecondMoment (q'.map f) := by
    let : IsProbabilityMeasure (q'.map f) := inferInstance
    refine ⟨o,?_⟩
    calc
      (∫⁻ x,(edist x o)^2 ∂q'.map f) ≤ ∫⁻ x,(ENNReal.ofReal R)^2 ∂q'.map f := by
        apply lintegral_mono_ae
        have H : ∀ᵐ x ∂q'.map f,dist x o ≤ R := (ae_map_iff hf.aemeasurable (measurableSet_le (by fun_prop) measurable_const)).mpr hb
        filter_upwards [H] with x hx
        rw [edist_dist]
        exact pow_le_pow_left₀ bot_le (ENNReal.ofReal_le_ofReal hx) 2
      _ < ∞ := by simp
  have ha0 : q'.map Prod.fst ≪ m := by
    dsimp only [q']
    rw [Measure.map_smul _ measurable_fst.aemeasurable]
    exact hac0.smul_left _
  have ha1 : q'.map Prod.snd ≪ m := by
    dsimp only [q']
    rw [Measure.map_smul _ measurable_snd.aemeasurable]
    exact hac1.smul_left _
  obtain ⟨π,hπ,hgeo,hopt,_⟩ := hcd (q'.map Prod.fst) (q'.map Prod.snd) hp0 hp1
    (hmom Prod.fst measurable_fst (hr.mono fun _ hx => hx.1))
    (hmom Prod.snd measurable_snd (hr.mono fun _ hx => hx.2)) ha0 ha1
  obtain ⟨h0,h1⟩ := hopt.1.interpolation_endpoints
  refine ⟨q univ • π,?_,?_,?_⟩
  · change (q univ • π).map _ = _
    rw [Measure.map_smul _ (continuous_eval_const timeZero).measurable.aemeasurable]
    change q univ • interpolation π timeZero = _
    rw [h0,←Measure.map_smul _ measurable_fst.aemeasurable,hcancel]
  · change (q univ • π).map _ = _
    rw [Measure.map_smul _ (continuous_eval_const timeOne).measurable.aemeasurable]
    change q univ • interpolation π timeOne = _
    rw [h1,←Measure.map_smul _ measurable_snd.aemeasurable,hcancel]
  · rw [lintegral_smul_measure]
    change q univ * (∫⁻ γ,kineticAction γ ∂π) ≤ _
    calc
      _ ≤ q univ * QuadraticTransportCost q' := by
        gcongr
        exact (geodesic_plan_action_le_cost hgeo).trans (hopt.2 q' ⟨rfl,rfl⟩)
      _ = QuadraticTransportCost q := by
        change q univ • (∫⁻ p : X×X,(edist p.1 p.2)^2 ∂q') = ∫⁻ p : X×X,(edist p.1 p.2)^2 ∂q
        rw [←lintegral_smul_measure,hcancel]

lemma CurvatureDimension.lift_coupling {m : Measure X} {K N : ℝ}
    (hcd : CurvatureDimension m K N) (q : Measure (X×X)) [IsFiniteMeasure q]
    (hac0 : q.map Prod.fst ≪ m) (hac1 : q.map Prod.snd ≪ m) [Nonempty X] :
    ∃ π : Measure (Curve X), interpolation π timeZero = q.map Prod.fst ∧
      interpolation π timeOne = q.map Prod.snd ∧
      (∫⁻ γ,kineticAction γ ∂π) ≤ QuadraticTransportCost q := by
  let o : X := Classical.arbitrary X
  let S : ℕ → Set (X×X) := fun n => Metric.closedBall o n ×ˢ Metric.closedBall o n
  let T : ℕ → Set (X×X) := disjointed S
  have hS (n : ℕ) : MeasurableSet (S n) := Metric.isClosed_closedBall.measurableSet.prod Metric.isClosed_closedBall.measurableSet
  have hT (n : ℕ) : MeasurableSet (T n) := MeasurableSet.disjointed hS n
  have hcover : ⋃ n,T n = univ := by
    rw [iUnion_disjointed]
    apply eq_univ_of_forall
    intro p
    obtain ⟨n,hn⟩ := exists_nat_gt (max (dist p.1 o) (dist p.2 o))
    exact mem_iUnion.mpr ⟨n,⟨(le_max_left _ _).trans hn.le,(le_max_right _ _).trans hn.le⟩⟩
  have hsum : Measure.sum (fun n => q.restrict (T n)) = q := by
    rw [←Measure.restrict_iUnion (disjoint_disjointed S) hT,hcover,Measure.restrict_univ]
  have hex (n : ℕ) : ∃ π : Measure (Curve X),
      interpolation π timeZero = (q.restrict (T n)).map Prod.fst ∧
      interpolation π timeOne = (q.restrict (T n)).map Prod.snd ∧
      (∫⁻ γ,kineticAction γ ∂π) ≤ QuadraticTransportCost (q.restrict (T n)) := by
    apply hcd.lift_bounded_coupling (q.restrict (T n))
      ((Measure.absolutelyContinuous_of_le (Measure.map_mono Measure.restrict_le_self measurable_fst)).trans hac0)
      ((Measure.absolutelyContinuous_of_le (Measure.map_mono Measure.restrict_le_self measurable_snd)).trans hac1) o n
    filter_upwards [ae_restrict_mem (hT n)] with p hp
    exact disjointed_subset S n hp
  choose πs h0 h1 hA using hex
  refine ⟨Measure.sum πs,?_,?_,?_⟩
  · change (Measure.sum πs).map _ = _
    rw [Measure.map_sum (continuous_eval_const timeZero).measurable.aemeasurable]
    simp_rw [show ∀ n,(πs n).map (fun γ => γ timeZero) = (q.restrict (T n)).map Prod.fst from h0]
    rw [←Measure.map_sum measurable_fst.aemeasurable,hsum]
  · change (Measure.sum πs).map _ = _
    rw [Measure.map_sum (continuous_eval_const timeOne).measurable.aemeasurable]
    simp_rw [show ∀ n,(πs n).map (fun γ => γ timeOne) = (q.restrict (T n)).map Prod.snd from h1]
    rw [←Measure.map_sum measurable_snd.aemeasurable,hsum]
  · rw [lintegral_sum_measure]
    calc
      _ ≤ ∑' n,QuadraticTransportCost (q.restrict (T n)) := ENNReal.tsum_le_tsum hA
      _ = QuadraticTransportCost q := by simp only [QuadraticTransportCost]; rw [←lintegral_sum_measure,hsum]
end WeakHessian

end
end InlinedFile0

end OAI
