import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.BoundedEndpointTube
import OAI.Geometry.WeakHessian.Transport.PlanEnergy

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

variable {X : Type*} [MetricSpace X]

@[simp] lemma halfTime_one : halfTime timeOne = timeHalf := by
  apply Subtype.ext; norm_num [halfTime,timeOne,timeHalf]
@[simp] lemma rightTime_zero : rightTime timeZero = timeHalf := by
  apply Subtype.ext; norm_num [rightTime,timeZero,timeHalf]

lemma IsGeodesic.half_length {γ : Curve X} (hγ : IsGeodesic γ) :
    dist (halfCurve γ timeZero) (halfCurve γ timeOne) = dist (γ timeZero) (γ timeOne)/2 := by
  change dist (γ (halfTime timeZero)) (γ (halfTime timeOne)) = _
  rw [hγ]
  norm_num [halfTime,timeZero,timeOne]
  ring

lemma IsGeodesic.right_length {γ : Curve X} (hγ : IsGeodesic γ) :
    dist (rightCurve γ timeZero) (rightCurve γ timeOne) = dist (γ timeZero) (γ timeOne)/2 := by
  change dist (γ (rightTime timeZero)) (γ (rightTime timeOne)) = _
  rw [hγ]
  norm_num [rightTime,timeZero,timeOne]
  ring

lemma IsGeodesic.halfCurve {γ : Curve X} (hγ : IsGeodesic γ) : IsGeodesic (halfCurve γ) := by
  intro s t
  rw [hγ.half_length]
  change dist (γ (halfTime s)) (γ (halfTime t)) = _
  rw [hγ]
  have H := dist_halfTime s t
  change |(halfTime s:ℝ)-(halfTime t:ℝ)| = |(s:ℝ)-(t:ℝ)|/2 at H
  rw [H]; ring

lemma IsGeodesic.rightCurve {γ : Curve X} (hγ : IsGeodesic γ) : IsGeodesic (rightCurve γ) := by
  intro s t
  rw [hγ.right_length]
  change dist (γ (rightTime s)) (γ (rightTime t)) = _
  rw [hγ]
  have H := dist_rightTime s t
  change |(rightTime s:ℝ)-(rightTime t:ℝ)| = |(s:ℝ)-(t:ℝ)|/2 at H
  rw [H]; ring

variable [MeasurableSpace X] [BorelSpace X]

lemma interpolation_map_half (π : Measure (Curve X)) (t : Time) :
    interpolation (π.map halfCurve) t = interpolation π (halfTime t) := by
  rw [interpolation,Measure.map_map (continuous_eval_const t).measurable continuous_halfCurve.measurable]
  rfl
lemma interpolation_map_right (π : Measure (Curve X)) (t : Time) :
    interpolation (π.map rightCurve) t = interpolation π (rightTime t) := by
  rw [interpolation,Measure.map_map (continuous_eval_const t).measurable continuous_rightCurve.measurable]
  rfl

omit [MeasurableSpace X] [BorelSpace X] in
lemma integrable_plan_energy_half {π : Measure (Curve X)}
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hI : Integrable (fun γ => dist (γ timeZero) (γ timeOne)^2) π) :
    Integrable (fun γ => dist (γ timeZero) (γ timeOne)^2) (π.map halfCurve) := by
  apply (integrable_map_measure plan_energy_measurable.aestronglyMeasurable continuous_halfCurve.measurable.aemeasurable).mpr
  apply (hI.div_const 4).congr
  filter_upwards [hg] with γ hγ
  dsimp only [Function.comp_def]
  rw [hγ.half_length]
  ring

omit [MeasurableSpace X] [BorelSpace X] in
lemma integrable_plan_energy_right {π : Measure (Curve X)}
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hI : Integrable (fun γ => dist (γ timeZero) (γ timeOne)^2) π) :
    Integrable (fun γ => dist (γ timeZero) (γ timeOne)^2) (π.map rightCurve) := by
  apply (integrable_map_measure plan_energy_measurable.aestronglyMeasurable continuous_rightCurve.measurable.aemeasurable).mpr
  apply (hI.div_const 4).congr
  filter_upwards [hg] with γ hγ
  dsimp only [Function.comp_def]
  rw [hγ.right_length]
  ring

omit [MeasurableSpace X] [BorelSpace X] in
lemma planEnergy_half {π : Measure (Curve X)} (hg : ∀ᵐ γ ∂π, IsGeodesic γ) :
    planEnergy (π.map halfCurve) = planEnergy π/4 := by
  rw [planEnergy,integral_map continuous_halfCurve.measurable.aemeasurable plan_energy_measurable.aestronglyMeasurable]
  change _ = (∫ γ, dist (γ timeZero) (γ timeOne)^2 ∂π)/4
  rw [← integral_div]
  apply integral_congr_ae
  filter_upwards [hg] with γ hγ
  rw [hγ.half_length]; ring

omit [MeasurableSpace X] [BorelSpace X] in
lemma planEnergy_right {π : Measure (Curve X)} (hg : ∀ᵐ γ ∂π, IsGeodesic γ) :
    planEnergy (π.map rightCurve) = planEnergy π/4 := by
  rw [planEnergy,integral_map continuous_rightCurve.measurable.aemeasurable plan_energy_measurable.aestronglyMeasurable]
  change _ = (∫ γ, dist (γ timeZero) (γ timeOne)^2 ∂π)/4
  rw [← integral_div]
  apply integral_congr_ae
  filter_upwards [hg] with γ hγ
  rw [hγ.right_length]; ring

def OptimalPlansShort (μ₀ μ₁ : Measure X) (D : ℝ) : Prop :=
  ∀ π : Measure (Curve X), IsProbabilityMeasure π →
    (∀ᵐ γ ∂π, IsGeodesic γ) → IsOptimalCoupling (endpointCoupling π) μ₀ μ₁ →
      ∀ᵐ γ ∂π, dist (γ timeZero) (γ timeOne) ≤ D

lemma optimalPlansShort_of_ball {μ₀ μ₁ : Measure X} (o : X) (R : ℝ≥0)
    (hb₀ : μ₀ (Metric.closedBall o R)ᶜ = 0) (hb₁ : μ₁ (Metric.closedBall o R)ᶜ = 0) :
    OptimalPlansShort μ₀ μ₁ (2*R) := by
  intro π hp hg hopt
  let := hp
  let : IsProbabilityMeasure μ₀ := by rw [← hopt.1.interpolation_endpoints.1]; exact interpolation_probability π _
  let : IsProbabilityMeasure μ₁ := by rw [← hopt.1.interpolation_endpoints.2]; exact interpolation_probability π _
  have H := optimalPlan_supported_tube (μ₀ := ⟨μ₀,inferInstance⟩) (μ₁ := ⟨μ₁,inferInstance⟩)
    (⟨π,hp⟩ : ProbabilityMeasure (Curve X)) hg hopt.1 hb₀ hb₁
  exact (ae_iff.mpr H).mono fun _ h => boundedEndpointTube_length_le h

variable [SecondCountableTopology X]

lemma optimalPlan_energy_le {μ ν : Measure (Curve X)}
    (hopt : IsOptimalCoupling (endpointCoupling μ) (interpolation ν timeZero) (interpolation ν timeOne))
    (hIν : Integrable (fun γ => dist (γ timeZero) (γ timeOne)^2) ν) :
    Integrable (fun γ => dist (γ timeZero) (γ timeOne)^2) μ ∧ planEnergy μ ≤ planEnergy ν := by
  have hcost := hopt.2 _ (endpointCoupling_couples ν)
  have hfin : QuadraticTransportCost (endpointCoupling μ) ≠ ∞ := by
    apply ne_top_of_le_ne_top _ hcost
    rw [planCost_eq_ofReal_energy hIν]
    exact ENNReal.ofReal_ne_top
  have hIμ := integrable_plan_energy hfin
  refine ⟨hIμ,?_⟩
  rw [planCost_eq_ofReal_energy hIμ,planCost_eq_ofReal_energy hIν] at hcost
  exact (ENNReal.ofReal_le_ofReal_iff (planEnergy_nonneg ν)).mp hcost

theorem OptimalPlansShort.halves [CompleteSpace X] {μ₀ μ₁ : Measure X} {D : ℝ}
    (hshort : OptimalPlansShort μ₀ μ₁ D)
    (π : Measure (Curve X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hopt : IsOptimalCoupling (endpointCoupling π) μ₀ μ₁)
    (hI : Integrable (fun γ => dist (γ timeZero) (γ timeOne)^2) π) :
    OptimalPlansShort μ₀ (interpolation π timeHalf) (D/2) ∧
    OptimalPlansShort (interpolation π timeHalf) μ₁ (D/2) := by
  let l := π.map halfCurve
  let r := π.map rightCurve
  let : IsProbabilityMeasure l := inferInstance
  let : IsProbabilityMeasure r := inferInstance
  have hgl : ∀ᵐ γ ∂l, IsGeodesic γ := by
    apply (ae_map_iff continuous_halfCurve.measurable.aemeasurable isClosed_isGeodesic.measurableSet).mpr
    exact hg.mono fun _ => IsGeodesic.halfCurve
  have hgr : ∀ᵐ γ ∂r, IsGeodesic γ := by
    apply (ae_map_iff continuous_rightCurve.measurable.aemeasurable isClosed_isGeodesic.measurableSet).mpr
    exact hg.mono fun _ => IsGeodesic.rightCurve
  have hIl : Integrable (fun γ => dist (γ timeZero) (γ timeOne)^2) l := integrable_plan_energy_half hg hI
  have hIr : Integrable (fun γ => dist (γ timeZero) (γ timeOne)^2) r := integrable_plan_energy_right hg hI
  have hl0 : interpolation l timeZero = μ₀ := by rw [interpolation_map_half,halfTime_zero,hopt.1.interpolation_endpoints.1]
  have hl1 : interpolation l timeOne = interpolation π timeHalf := by rw [interpolation_map_half,halfTime_one]
  have hr0 : interpolation r timeZero = interpolation π timeHalf := by rw [interpolation_map_right,rightTime_zero]
  have hr1 : interpolation r timeOne = μ₁ := by rw [interpolation_map_right,rightTime_one,hopt.1.interpolation_endpoints.2]
  have hel : planEnergy l = planEnergy π/4 := planEnergy_half hg
  have her : planEnergy r = planEnergy π/4 := planEnergy_right hg
  constructor
  · intro η hpη hgη hoη
    let := hpη
    have hoη' : IsOptimalCoupling (endpointCoupling η) (interpolation l timeZero) (interpolation l timeOne) := by rwa [hl0,hl1]
    obtain ⟨hIη,heη⟩ := optimalPlan_energy_le hoη' hIl
    have hpush : interpolation η timeOne = interpolation r timeZero := by rw [hoη.1.interpolation_endpoints.2,hr0]
    have hoπ : IsOptimalCoupling (endpointCoupling π) (interpolation η timeZero) (interpolation r timeOne) := by rwa [hoη.1.interpolation_endpoints.1,hr1]
    obtain ⟨ω,hpω,hgω,hoω,_,_,hlω,_⟩ := exists_optimal_geodesic_join η r π hpush hgη hgr hIη hIr hI hoπ (by rw [hel] at heη; rw [her]; linarith)
    let := hpω
    have hωshort := hshort ω hpω hgω (by simpa only [hoη.1.interpolation_endpoints.1,hr1] using hoω)
    rw [← hlω]
    apply (ae_map_iff continuous_halfCurve.measurable.aemeasurable
      (measurableSet_le ((continuous_eval_const timeZero).dist (continuous_eval_const timeOne)).measurable measurable_const)).mpr
    filter_upwards [hgω,hωshort] with γ hγ hb
    rw [hγ.half_length]
    linarith
  · intro η hpη hgη hoη
    let := hpη
    have hoη' : IsOptimalCoupling (endpointCoupling η) (interpolation r timeZero) (interpolation r timeOne) := by rwa [hr0,hr1]
    obtain ⟨hIη,heη⟩ := optimalPlan_energy_le hoη' hIr
    have hpush : interpolation l timeOne = interpolation η timeZero := by rw [hoη.1.interpolation_endpoints.1,hl1]
    have hoπ : IsOptimalCoupling (endpointCoupling π) (interpolation l timeZero) (interpolation η timeOne) := by rwa [hl0,hoη.1.interpolation_endpoints.2]
    obtain ⟨ω,hpω,hgω,hoω,_,_,_,hrω⟩ := exists_optimal_geodesic_join l η π hpush hgl hgη hIl hIη hI hoπ (by rw [her] at heη; rw [hel]; linarith)
    let := hpω
    have hωshort := hshort ω hpω hgω (by simpa only [hl0,hoη.1.interpolation_endpoints.2] using hoω)
    rw [← hrω]
    apply (ae_map_iff continuous_rightCurve.measurable.aemeasurable
      (measurableSet_le ((continuous_eval_const timeZero).dist (continuous_eval_const timeOne)).measurable measurable_const)).mpr
    filter_upwards [hgω,hωshort] with γ hγ hb
    rw [hγ.right_length]
    linarith

omit [SecondCountableTopology X] in
lemma OptimalPlansShort.subplan {μ₀ μ₁ : Measure X} {D : ℝ}
    (hshort : OptimalPlansShort μ₀ μ₁ D)
    (π : Measure (Curve X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hopt : IsOptimalCoupling (endpointCoupling π) μ₀ μ₁)
    (θ : Measure (Curve X)) (hθ : θ ≤ π) (hq : θ univ ≠ 0) :
    OptimalPlansShort (interpolation ((θ univ)⁻¹ • θ) timeZero)
      (interpolation ((θ univ)⁻¹ • θ) timeOne) D := by
  let : IsFiniteMeasure θ := isFiniteMeasure_of_le π hθ
  let q := θ univ
  have hqt : q ≠ ∞ := measure_ne_top _ _
  let θ' := q⁻¹ • θ
  have hcanc : q • θ' = θ := by
    dsimp only [θ']; rw [smul_smul,ENNReal.mul_inv_cancel hq hqt,one_smul]
  intro η hpη hgη hoη
  let := hpη
  let ξ := q • η
  have hξmass : ξ univ = θ univ := by simp [ξ,q]
  have hξend (t : Time) (h : interpolation η t = interpolation θ' t) :
      interpolation ξ t = interpolation θ t := by
    change (q • η).map _ = θ.map _
    rw [Measure.map_smul _ (continuous_eval_const t).measurable.aemeasurable]
    change q • interpolation η t = _
    rw [h]
    change q • θ'.map _ = _
    rw [← Measure.map_smul _ (continuous_eval_const t).measurable.aemeasurable,hcanc]
  have hξ0 := hξend timeZero hoη.1.interpolation_endpoints.1
  have hξ1 := hξend timeOne hoη.1.interpolation_endpoints.2
  have hcost : QuadraticTransportCost (endpointCoupling ξ) ≤ QuadraticTransportCost (endpointCoupling θ) := by
    have H := mul_le_mul' (le_refl q) (hoη.2 _ (endpointCoupling_couples θ'))
    have hs (ρ : Measure (Curve X)) : QuadraticTransportCost (endpointCoupling (q • ρ)) =
        q*QuadraticTransportCost (endpointCoupling ρ) := by
      simp only [QuadraticTransportCost,endpointCoupling,
        Measure.map_smul _ ((continuous_eval_const timeZero).measurable.prodMk
          (continuous_eval_const timeOne).measurable).aemeasurable,
        lintegral_smul_measure,smul_eq_mul]
    rw [← hs η,← hs θ',hcanc] at H
    exact H
  have hgξ : ∀ᵐ γ ∂ξ, IsGeodesic γ := (Measure.AbsolutelyContinuous.rfl.smul_left _).ae_le hgη
  let ω := π-θ+ξ
  have hpω : IsProbabilityMeasure ω := replacement_probability _ _ _ hθ hξmass
  have H := hshort ω hpω (geodesic_plan_reroute hg hgξ) (hopt.reroute_plan hθ hξ0 hξ1 hcost)
  have hξω : ξ ≤ ω := by
    have H := add_le_add (show (0 : Measure (Curve X)) ≤ π-θ from bot_le) (le_refl ξ)
    simpa only [zero_add] using H
  exact (Measure.absolutelyContinuous_smul hq).ae_le ((Measure.absolutelyContinuous_of_le hξω).ae_le H)

end WeakHessian

end
end InlinedFile0

end OAI
