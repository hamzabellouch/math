import Mathlib
import OAI.Geometry.WeakHessian.Calculus.RnDerivRestrictReference
import OAI.Geometry.WeakHessian.Entropy.CenteredMulLogDeriv
import OAI.Geometry.WeakHessian.Entropy.EntropyCell
import OAI.Geometry.WeakHessian.Geodesics.Join

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
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Filter
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter Topology

namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

universe u
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [SecondCountableTopology X] [ProperSpace X]
variable {m : Measure X} [SigmaFinite m] {K N : ℝ}

def lawAt (π : ProbabilityMeasure (Curve X)) (t : Time) : ProbabilityMeasure X :=
  π.map (fun γ => γ t)

omit [BorelSpace X] [SecondCountableTopology X] [ProperSpace X] in
lemma lawAt_coe (π : ProbabilityMeasure (Curve X)) (t : Time) :
    (lawAt π t:Measure X) = interpolation (π:Measure (Curve X)) t := rfl

omit [SecondCountableTopology X] [ProperSpace X] in
lemma continuous_lawAt_plan (t : Time) : Continuous (fun π : ProbabilityMeasure (Curve X) => lawAt π t) :=
  ProbabilityMeasure.continuous_map (continuous_eval_const t)

omit [SecondCountableTopology X] [ProperSpace X] in
lemma continuous_lawAt_time (π : ProbabilityMeasure (Curve X)) : Continuous (lawAt π) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuous_integral.mpr
  intro f
  have he (t : Time) : (∫ x, f x ∂(lawAt π t:Measure X)) = ∫ γ, f (γ t) ∂(π:Measure (Curve X)) :=
    integral_map (continuous_eval_const t).measurable.aemeasurable f.continuous.aestronglyMeasurable
  simp_rw [he]
  apply continuous_of_dominated (bound := fun _ => ‖f‖)
  · intro t; exact (f.continuous.comp (continuous_eval_const t)).aestronglyMeasurable
  · intro t; exact ae_of_all _ fun γ => f.norm_coe_le_norm (γ t)
  · exact integrable_const ‖f‖
  · exact ae_of_all _ fun γ => f.continuous.comp γ.continuous

def cellPlanFamily (c : EntropyCell m K N) : Set (ProbabilityMeasure (Curve X)) :=
  {π | (∀ᵐ γ ∂(π:Measure (Curve X)), IsGeodesic γ) ∧
    IsOptimalCoupling (endpointCoupling (π:Measure (Curve X))) c.leftLaw c.rightLaw}

omit [SigmaFinite m] in
lemma isCompact_cellPlanFamily (c : EntropyCell m K N) (p : CellPlan c) :
    IsCompact (cellPlanFamily c) := by
  let cost := ∫ γ, clippedEndpointCost c.radius γ ∂(p.law:Measure (Curve X))
  have hc : 0 ≤ cost := integral_nonneg (clippedEndpointCost_nonneg c.radius)
  have hps := optimalPlan_supported_tube p.law p.geodesic p.optimal.1 c.left_supported c.right_supported
  have hcostp := endpointCost_eq_clipped_integral (p.law:Measure (Curve X)) hps
  have he : cellPlanFamily c = {π : ProbabilityMeasure (Curve X) |
      (π:Measure (Curve X)) (boundedEndpointTube c.center c.radius)ᶜ = 0 ∧
      lawAt π timeZero = c.leftLaw ∧ lawAt π timeOne = c.rightLaw ∧
      (∫ γ, clippedEndpointCost c.radius γ ∂(π:Measure (Curve X))) ≤ cost} := by
    ext π
    constructor
    · rintro ⟨hg,ho⟩
      have hs := optimalPlan_supported_tube π hg ho.1 c.left_supported c.right_supported
      refine ⟨hs,Subtype.ext ho.1.interpolation_endpoints.1,Subtype.ext ho.1.interpolation_endpoints.2,?_⟩
      apply (ENNReal.ofReal_le_ofReal_iff hc).mp
      rw [← endpointCost_eq_clipped_integral (π:Measure (Curve X)) hs,← hcostp]
      exact ho.2 _ p.optimal.1
    · rintro ⟨hs,h0,h1,hcost⟩
      have hend : IsCoupling (endpointCoupling (π:Measure (Curve X))) c.leftLaw c.rightLaw := by
        have H := endpointCoupling_couples (π:Measure (Curve X))
        have h0' : interpolation (π:Measure (Curve X)) timeZero = (c.leftLaw:Measure X) := congrArg Subtype.val h0
        have h1' : interpolation (π:Measure (Curve X)) timeOne = (c.rightLaw:Measure X) := congrArg Subtype.val h1
        rwa [h0',h1'] at H
      refine ⟨(ae_iff.mpr hs).mono (fun γ hγ => hγ.1),hend,?_⟩
      intro q hq
      apply le_trans ?_ (p.optimal.2 q hq)
      rw [endpointCost_eq_clipped_integral (π:Measure (Curve X)) hs,hcostp]
      exact ENNReal.ofReal_le_ofReal hcost
  rw [he]
  apply (isCompact_probability_supported (isCompact_boundedEndpointTube c.center c.radius)).inter_right
  exact (isClosed_eq (continuous_lawAt_plan timeZero) continuous_const).inter
    ((isClosed_eq (continuous_lawAt_plan timeOne) continuous_const).inter
      (isClosed_le (ProbabilityMeasure.continuous_integral_boundedContinuousFunction _) continuous_const))
omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [ProperSpace X] in
lemma IsGeodesic.speed_energy_le {γ : Curve X} (hγ : IsGeodesic γ) :
    (∫⁻ t in Icc (0:ℝ) 1, (metricSpeed γ t)^2) ≤ ENNReal.ofReal (dist (γ timeZero) (γ timeOne)^2) := by
  calc
    _ ≤ ∫⁻ _t in Icc (0:ℝ) 1, (ENNReal.ofReal (dist (γ timeZero) (γ timeOne)))^2 := by
      apply lintegral_mono_ae
      exact hγ.squareControl.metricSpeed_le.mono fun t ht => pow_le_pow_left' ht 2
    _ = _ := by simp only [lintegral_const,Measure.restrict_apply_univ,Real.volume_Icc,
        sub_zero,ENNReal.ofReal_one,mul_one,ENNReal.ofReal_pow dist_nonneg]

namespace CDEnvironment
variable (env : CDEnvironment m K N)

def stablePlanFamily (c : EntropyCell m K N) (n : ℕ) : Set (ProbabilityMeasure (Curve X)) :=
  cellPlanFamily c ∩ {π | ∀ t ∈ dyadicTimes n, lawAt π t = lawAt (env.build n c).law t}

lemma stablePlanFamily_closed (c : EntropyCell m K N) (n : ℕ) :
    IsClosed (env.stablePlanFamily c n) := by
  apply (isCompact_cellPlanFamily c (env.build 0 c)).isClosed.inter
  have he : {π : ProbabilityMeasure (Curve X) | ∀ t ∈ dyadicTimes n,
      lawAt π t = lawAt (env.build n c).law t} =
      ⋂ t : Time, ⋂ (_ : t ∈ dyadicTimes n), {π | lawAt π t = lawAt (env.build n c).law t} := by
    ext π; simp only [mem_ofPred_eq,mem_iInter]
  rw [he]
  exact isClosed_iInter fun t => isClosed_iInter fun _ => isClosed_eq (continuous_lawAt_plan t) continuous_const

lemma exists_stable_plan (c : EntropyCell m K N) :
    ∃ p : CellPlan c, ∀ n t, t ∈ dyadicTimes n →
      interpolation (p.law:Measure (Curve X)) t = interpolation ((env.build n c).law:Measure (Curve X)) t := by
  have hmono (n : ℕ) : env.stablePlanFamily c (n+1) ⊆ env.stablePlanFamily c n := by
    intro π hπ
    refine ⟨hπ.1,fun t ht => ?_⟩
    rw [hπ.2 t (monotone_dyadicTimes (Nat.le_succ n) ht)]
    exact Subtype.ext (env.build_stable n (n+1) (Nat.le_succ n) c t ht)
  have hne (n : ℕ) : (env.stablePlanFamily c n).Nonempty :=
    ⟨(env.build n c).law,⟨(env.build n c).geodesic,(env.build n c).optimal⟩,fun _ _ => rfl⟩
  have hc : IsCompact (env.stablePlanFamily c 0) :=
    (isCompact_cellPlanFamily c (env.build 0 c)).of_isClosed_subset (env.stablePlanFamily_closed c 0) inter_subset_left
  obtain ⟨π,hπ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (env.stablePlanFamily c) hmono hne hc (env.stablePlanFamily_closed c)
  have hπs := mem_iInter.mp hπ
  refine ⟨⟨π,(hπs 0).1.1,(hπs 0).1.2⟩,fun n t ht => ?_⟩
  exact congrArg Subtype.val ((hπs n).2 t ht)

noncomputable def limitPlan (c : EntropyCell m K N) : CellPlan c :=
  Classical.choose (env.exists_stable_plan c)

lemma limitPlan_dyadic (c : EntropyCell m K N) (n : ℕ) (t : Time) (ht : t ∈ dyadicTimes n) :
    interpolation ((env.limitPlan c).law:Measure (Curve X)) t =
      interpolation ((env.build n c).law:Measure (Curve X)) t :=
  Classical.choose_spec (env.exists_stable_plan c) n t ht

lemma limitPlan_finite_entropy_dyadic (c : EntropyCell m K N) (n : ℕ) (t : Time) (ht : t ∈ dyadicTimes n) :
    FiniteEntropy m (interpolation ((env.limitPlan c).law:Measure (Curve X)) t) := by
  rw [env.limitPlan_dyadic c n t ht]
  exact env.build_finite_entropy n c t ht

lemma limitPlan_entropy_bound_dyadic (c : EntropyCell m K N) (n : ℕ) (t : Time) (ht : t ∈ dyadicTimes n) :
    entropyReal m (interpolation ((env.limitPlan c).law:Measure (Curve X)) t) ≤
      (1-(t:ℝ))*entropyReal m (c.leftLaw:Measure X)+(t:ℝ)*entropyReal m (c.rightLaw:Measure X) -
        K/2*((t:ℝ)*(1-(t:ℝ)))*planEnergy ((env.limitPlan c).law:Measure (Curve X)) := by
  rw [env.limitPlan_dyadic c n t ht,(env.limitPlan c).energy_eq (env.build n c)]
  exact env.build_entropy_bound n c t ht

lemma limitPlan_dominated_dyadic (c : EntropyCell m K N) (n : ℕ) (t : Time) (ht : t ∈ dyadicTimes n) :
    interpolation ((env.limitPlan c).law:Measure (Curve X)) t ≤ c.uniformCap • m := by
  rw [env.limitPlan_dyadic c n t ht]
  exact env.build_dominated n c t ht

lemma limitPlan_dominated (c : EntropyCell m K N) (t : Time) :
    interpolation ((env.limitPlan c).law:Measure (Curve X)) t ≤ c.uniformCap • m := by
  let Q := Metric.closedBall c.center (3*(c.radius:ℝ))
  let : IsFiniteMeasure (m.restrict Q) := ⟨by
    simpa only [Measure.restrict_apply_univ] using env.finite_bounded Q Metric.isBounded_closedBall⟩
  have hnu : IsFiniteMeasure (c.uniformCap • m.restrict Q) := ⟨by
    rw [Measure.smul_apply,smul_eq_mul]
    exact ENNReal.mul_lt_top c.uniformCap_finite.lt_top (measure_lt_top _ _)⟩
  let := hnu
  have hclosed : IsClosed {s : Time |
      (lawAt (env.limitPlan c).law s:Measure X) ≤ c.uniformCap • m.restrict Q} :=
    (isClosed_probability_dominated _).preimage (continuous_lawAt_time _)
  have hdyadic : (⋃ n, dyadicTimes n) ⊆ {s : Time |
      (lawAt (env.limitPlan c).law s:Measure X) ≤ c.uniformCap • m.restrict Q} := by
    intro s hs
    obtain ⟨n,hn⟩ := mem_iUnion.mp hs
    have hd := env.limitPlan_dominated_dyadic c n s hn
    have hsupport : interpolation ((env.limitPlan c).law:Measure (Curve X)) s Qᶜ = 0 :=
      geodesic_plan_supported_ball _ (env.limitPlan c).geodesic c.center c.radius
        (by rw [(env.limitPlan c).optimal.1.interpolation_endpoints.1]; exact c.left_supported)
        (by rw [(env.limitPlan c).optimal.1.interpolation_endpoints.2]; exact c.right_supported) s
    have H := Measure.restrict_mono_measure hd Q
    rwa [Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hsupport),Measure.restrict_smul] at H
  have H : (lawAt (env.limitPlan c).law t:Measure X) ≤ c.uniformCap • m.restrict Q :=
    (closure_minimal hdyadic hclosed) (dense_dyadicTimes t)
  exact H.trans (smul_le_smul_left _ Measure.restrict_le_self)

lemma limitPlan_supported (c : EntropyCell m K N) (t : Time) :
    interpolation ((env.limitPlan c).law:Measure (Curve X)) t (Metric.closedBall c.center (3*(c.radius:ℝ)))ᶜ = 0 :=
  geodesic_plan_supported_ball _ (env.limitPlan c).geodesic c.center c.radius
    (by rw [(env.limitPlan c).optimal.1.interpolation_endpoints.1]; exact c.left_supported)
    (by rw [(env.limitPlan c).optimal.1.interpolation_endpoints.2]; exact c.right_supported) t

lemma limitPlan_finite_entropy (c : EntropyCell m K N) (t : Time) :
    FiniteEntropy m (interpolation ((env.limitPlan c).law:Measure (Curve X)) t) := by
  let Q := Metric.closedBall c.center (3*(c.radius:ℝ))
  let : IsFiniteMeasure (m.restrict Q) := ⟨by
    simpa only [Measure.restrict_apply_univ] using env.finite_bounded Q Metric.isBounded_closedBall⟩
  let : IsProbabilityMeasure (interpolation ((env.limitPlan c).law:Measure (Curve X)) t) :=
    interpolation_probability _ _
  have hs : ∀ᵐ x ∂interpolation ((env.limitPlan c).law:Measure (Curve X)) t, x ∈ Q :=
    ae_iff.mpr (env.limitPlan_supported c t)
  apply (finiteEntropy_restrict_reference_iff Metric.isClosed_closedBall.measurableSet hs).mp
  apply finiteEntropy_of_bounded_density c.uniformCap_finite
  have H := Measure.restrict_mono_measure (env.limitPlan_dominated c t) Q
  rwa [Measure.restrict_eq_self_of_ae_mem hs,Measure.restrict_smul] at H

lemma limitPlan_boundedTracks (c : EntropyCell m K N) :
    BoundedTracks ((env.limitPlan c).law:Measure (Curve X)) := by
  refine ⟨c.center,3*(c.radius:ℝ)+1,by positivity,?_⟩
  have H := optimalPlan_supported_tube (env.limitPlan c).law (env.limitPlan c).geodesic
    (env.limitPlan c).optimal.1 c.left_supported c.right_supported
  filter_upwards [ae_iff.mpr H] with γ hγ
  intro t
  exact (boundedEndpointTube_range hγ t).trans (by linarith)

lemma limitPlan_isTestPlan (c : EntropyCell m K N) :
    IsTestPlan m ((env.limitPlan c).law:Measure (Curve X)) := by
  refine ⟨inferInstance,⟨c.uniformCap.toNNReal,?_⟩,?_,?_⟩
  · intro t
    rw [ENNReal.coe_toNNReal c.uniformCap_finite]
    exact env.limitPlan_dominated c t
  · exact (env.limitPlan c).geodesic.mono fun γ hγ => hγ.squareControl.isAC2
  · have hB : (∫⁻ γ, ∫⁻ t in Icc (0:ℝ) 1, (metricSpeed γ t)^2
        ∂volume ∂((env.limitPlan c).law:Measure (Curve X))) ≤ ENNReal.ofReal ((c.length:ℝ)^2) := by
      calc
        _ ≤ ∫⁻ _γ, ENNReal.ofReal ((c.length:ℝ)^2) ∂((env.limitPlan c).law:Measure (Curve X)) := by
          apply lintegral_mono_ae
          filter_upwards [(env.limitPlan c).geodesic,
            c.short _ inferInstance (env.limitPlan c).geodesic (env.limitPlan c).optimal] with γ hγ hlen
          exact hγ.speed_energy_le.trans (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ dist_nonneg hlen 2))
        _ = _ := by simp only [lintegral_const,measure_univ,mul_one]
    exact hB.trans_lt ENNReal.ofReal_lt_top

end CDEnvironment
end WeakHessian

end
end InlinedFile0

end OAI
