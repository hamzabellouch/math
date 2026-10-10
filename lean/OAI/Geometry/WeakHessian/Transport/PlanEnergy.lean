import Mathlib
import OAI.Geometry.WeakHessian.Curvature.Nonbranching
import OAI.Geometry.WeakHessian.Calculus.RnDerivSmul

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
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter

attribute [local instance] Classical.propDecidable
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


open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set Filter Topology


namespace WeakHessian
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

lemma integrable_squared_distance_of_cost [SecondCountableTopology X] {q : Measure (X×X)}
    (hq : QuadraticTransportCost q ≠ ∞) : Integrable (fun p : X×X => dist p.1 p.2^2) q := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (measurable_fst.dist measurable_snd |>.pow_const 2).aestronglyMeasurable
    (ae_of_all _ fun _ => sq_nonneg _)).mp
  simpa only [QuadraticTransportCost,edist_dist,ENNReal.ofReal_pow dist_nonneg] using hq

lemma quadraticTransportCost_eq_integral [SecondCountableTopology X] {q : Measure (X×X)}
    (hq : QuadraticTransportCost q ≠ ∞) :
    QuadraticTransportCost q = ENNReal.ofReal (∫ p : X×X, dist p.1 p.2^2 ∂q) := by
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_squared_distance_of_cost hq)
    (ae_of_all _ fun _ => sq_nonneg _)]
  simp only [QuadraticTransportCost,edist_dist,ENNReal.ofReal_pow dist_nonneg]

omit [BorelSpace X] in
lemma cost_ne_top_of_bounded {q : Measure (X×X)} [IsFiniteMeasure q] {D : ℝ}
    (hD : ∀ᵐ p ∂q, dist p.1 p.2 ≤ D) : QuadraticTransportCost q ≠ ∞ := by
  have hp : ∀ᵐ p ∂q, (edist p.1 p.2)^2 ≤ (ENNReal.ofReal D)^2 := by
    filter_upwards [hD] with p hp
    rw [edist_dist]
    exact pow_le_pow_left₀ bot_le (ENNReal.ofReal_le_ofReal hp) 2
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (by simp) (measure_ne_top _ _))
    ((lintegral_mono_ae hp).trans_eq (lintegral_const _))

omit [MeasurableSpace X] [BorelSpace X] in
lemma quadratic_triangle_rigidity {A : Type*} [MeasurableSpace A] {q : Measure A}
    (x y z : A → X)
    (hx : Integrable (fun a => dist (x a) (y a)^2) q)
    (hy : Integrable (fun a => dist (y a) (z a)^2) q)
    (hz : Integrable (fun a => dist (x a) (z a)^2) q)
    (he : (∫ a, dist (x a) (z a)^2 ∂q) ≥
      2*((∫ a, dist (x a) (y a)^2 ∂q)+(∫ a, dist (y a) (z a)^2 ∂q))) :
    ∀ᵐ a ∂q, dist (x a) (y a) = dist (y a) (z a) ∧
      dist (x a) (z a) = 2*dist (x a) (y a) := by
  have hnon : ∀ a, 0 ≤ 2*(dist (x a) (y a)^2+dist (y a) (z a)^2)-dist (x a) (z a)^2 := by
    intro a
    have ht := dist_triangle (x a) (y a) (z a)
    have hd := dist_nonneg (x := x a) (y := z a)
    nlinarith [sq_nonneg (dist (x a) (y a)-dist (y a) (z a))]
  have hadd : Integrable (fun a => dist (x a) (y a)^2+dist (y a) (z a)^2) q := hx.add hy
  have htw : Integrable (fun a => 2*(dist (x a) (y a)^2+dist (y a) (z a)^2)) q := hadd.const_mul 2
  have hi := htw.sub hz
  have hi0 : (∫ a, 2*(dist (x a) (y a)^2+dist (y a) (z a)^2)-dist (x a) (z a)^2 ∂q) = 0 := by
    apply le_antisymm
    · rw [integral_sub htw hz, integral_const_mul, integral_add hx hy]
      linarith
    · exact integral_nonneg hnon
  have hae := (integral_eq_zero_iff_of_nonneg hnon hi).mp hi0
  filter_upwards [hae] with a ha
  have ht := dist_triangle (x a) (y a) (z a)
  have hd := dist_nonneg (x := x a) (y := z a)
  have hx0 := dist_nonneg (x := x a) (y := y a)
  have hy0 := dist_nonneg (x := y a) (y := z a)
  dsimp only [Pi.zero_apply] at ha
  have heq : dist (x a) (y a) = dist (y a) (z a) := by
    nlinarith [sq_nonneg (dist (x a) (z a)),sq_nonneg (dist (x a) (y a)-dist (y a) (z a))]
  refine ⟨heq,?_⟩
  nlinarith [sq_nonneg (dist (x a) (z a)-2*dist (x a) (y a))]

omit [MeasurableSpace X] [BorelSpace X] in
lemma joinCurve_isGeodesic {γ η : Curve X} (hjoin : γ timeOne = η timeZero)
    (hγ : IsGeodesic γ) (hη : IsGeodesic η)
    (hlen : dist (γ timeZero) (γ timeOne) = dist (η timeZero) (η timeOne))
    (hend : dist (γ timeZero) (η timeOne) = 2*dist (γ timeZero) (γ timeOne)) :
    IsGeodesic (joinCurve γ η hjoin) := by
  let L : ℝ≥0 := 2*nndist (γ timeZero) (γ timeOne)
  have hγlen : dist (γ timeZero) (γ timeOne) = ((1/2:ℝ)-0)*(L:ℝ) := by
    dsimp [L]; ring
  have hηlen : dist (η timeZero) (η timeOne) = ((1:ℝ)-1/2)*(L:ℝ) := by
    rw [← hlen]; dsimp [L]; ring
  have hgl := hγ.stretch_lipschitzWith (0:ℝ) (1/2) (by norm_num) hγlen
  have hel := hη.stretch_lipschitzWith (1/2:ℝ) 1 (by norm_num) hηlen
  have heq : evalReal γ (((1/2:ℝ)-0)/(1/2-0)) = evalReal η (((1/2:ℝ)-1/2)/(1-1/2)) := by
    norm_num only [sub_zero,sub_self,zero_div,div_self (by norm_num : (1/2:ℝ) ≠ 0)]
    simpa only [evalReal_one,evalReal_zero] using hjoin
  have hl := lipschitzWith_if_le (1/2:ℝ) hgl hel heq
  have hj (t : Time) : joinCurve γ η hjoin t =
      if (t:ℝ) ≤ 1/2 then evalReal γ (((t:ℝ)-0)/(1/2-0)) else
        evalReal η (((t:ℝ)-1/2)/(1-1/2)) := by
    split_ifs with ht
    · rw [joinCurve_apply_left _ _ _ t ht]; congr 1; ring
    · rw [joinCurve_apply_right _ _ _ t (le_of_not_ge ht)]; congr 1; ring
  apply isGeodesic_of_dist_le
  intro s t
  rw [joinCurve_zero,joinCurve_one,hend,hj s,hj t]
  convert hl.dist_le_mul (s:ℝ) (t:ℝ) using 1
  dsimp [L]
  simp only [Real.dist_eq]
  ring

variable [SecondCountableTopology X]

def planEnergy (π : Measure (Curve X)) : ℝ := ∫ γ, dist (γ timeZero) (γ timeOne)^2 ∂π

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
lemma plan_energy_measurable : Measurable (fun γ : Curve X => dist (γ timeZero) (γ timeOne)^2) :=
  ((continuous_eval_const timeZero).dist (continuous_eval_const timeOne)).measurable.pow_const 2

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
lemma planEnergy_nonneg (π : Measure (Curve X)) : 0 ≤ planEnergy π :=
  integral_nonneg fun _ => sq_nonneg _

lemma planCost_eq_ofReal_energy {π : Measure (Curve X)}
    (hI : Integrable (fun γ => dist (γ timeZero) (γ timeOne)^2) π) :
    QuadraticTransportCost (endpointCoupling π) = ENNReal.ofReal (planEnergy π) := by
  rw [QuadraticTransportCost,endpointCoupling,
    lintegral_map (measurable_fst.edist measurable_snd |>.pow_const 2)
      ((continuous_eval_const timeZero).measurable.prodMk (continuous_eval_const timeOne).measurable)]
  rw [planEnergy,ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ fun _ => sq_nonneg _)]
  simp only [edist_dist,ENNReal.ofReal_pow dist_nonneg]

lemma integrable_plan_energy {π : Measure (Curve X)}
    (hπ : QuadraticTransportCost (endpointCoupling π) ≠ ∞) :
    Integrable (fun γ => dist (γ timeZero) (γ timeOne)^2) π := by
  have hi := integrable_squared_distance_of_cost hπ
  exact (integrable_map_measure
    (measurable_fst.dist measurable_snd |>.pow_const 2).aestronglyMeasurable
    ((continuous_eval_const timeZero).measurable.prodMk (continuous_eval_const timeOne).measurable).aemeasurable).mp hi
lemma exists_joinable_gluing [CompleteSpace X]
    (μ ν : Measure (Curve X)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hpush : interpolation μ timeOne = interpolation ν timeZero) :
    ∃ q : Measure (Joinable X), IsProbabilityMeasure q ∧
      q.map (fun p => p.1.1) = μ ∧ q.map (fun p => p.1.2) = ν := by
  let : Nonempty (Curve X) := nonempty_of_isProbabilityMeasure μ
  let E := {p : Curve X × Curve X | p.1 timeOne = p.2 timeZero}
  have hE : MeasurableSet E := isClosed_joinable.measurableSet
  obtain ⟨q,hqp,hq0,hq1,hqE⟩ := WeakHessianTransport.exists_fiber_gluing_supported μ ν
    (fun γ => γ timeOne) (fun γ => γ timeZero) (continuous_eval_const _).measurable
    (continuous_eval_const _).measurable hpush
  let := hqp
  let qs : Measure (Joinable X) := q.comap Subtype.val
  have hemb : MeasurableEmbedding (Subtype.val : Joinable X → Curve X × Curve X) :=
    MeasurableEmbedding.subtype_coe hE
  have hsupp : ∀ᵐ p ∂q, p ∈ range (Subtype.val : Joinable X → Curve X×Curve X) := by
    simpa only [Subtype.range_coe_subtype, mem_ofPred_eq] using hqE
  let : IsProbabilityMeasure qs := hemb.isProbabilityMeasure_comap hsupp
  have hqs : qs.map Subtype.val = q := by
    rw [hemb.map_comap, Measure.restrict_eq_self_of_ae_mem hsupp]
  refine ⟨qs,inferInstance,?_,?_⟩
  · rw [← hq0, ← hqs, Measure.map_map measurable_fst hemb.measurable]; rfl
  · rw [← hq1, ← hqs, Measure.map_map measurable_snd hemb.measurable]; rfl

def halfCurve (γ : Curve X) : Curve X := γ.comp ⟨halfTime,continuous_halfTime⟩
def rightCurve (γ : Curve X) : Curve X := γ.comp ⟨rightTime,continuous_rightTime⟩
omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
lemma continuous_halfCurve : Continuous (halfCurve (X := X)) := ContinuousMap.continuous_precomp _
omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
lemma continuous_rightCurve : Continuous (rightCurve (X := X)) := ContinuousMap.continuous_precomp _

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
lemma halfCurve_joinCurve (γ η : Curve X) (h : γ timeOne = η timeZero) :
    halfCurve (joinCurve γ η h) = γ := by
  ext t; exact joinCurve_halfTime γ η h t
omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
lemma rightCurve_joinCurve (γ η : Curve X) (h : γ timeOne = η timeZero) :
    rightCurve (joinCurve γ η h) = η := by
  ext t; exact joinCurve_rightTime γ η h t

theorem exists_optimal_geodesic_join [CompleteSpace X]
    (μ ν ρ : Measure (Curve X)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ρ]
    (hpush : interpolation μ timeOne = interpolation ν timeZero)
    (hgμ : ∀ᵐ γ ∂μ, IsGeodesic γ) (hgν : ∀ᵐ γ ∂ν, IsGeodesic γ)
    (hIμ : Integrable (fun γ => dist (γ timeZero) (γ timeOne)^2) μ)
    (hIν : Integrable (fun γ => dist (γ timeZero) (γ timeOne)^2) ν)
    (hIρ : Integrable (fun γ => dist (γ timeZero) (γ timeOne)^2) ρ)
    (hρ : IsOptimalCoupling (endpointCoupling ρ) (interpolation μ timeZero) (interpolation ν timeOne))
    (hbudget : 2*(planEnergy μ+planEnergy ν) ≤ planEnergy ρ) :
    ∃ π : Measure (Curve X), IsProbabilityMeasure π ∧
      (∀ᵐ γ ∂π, IsGeodesic γ) ∧
      IsOptimalCoupling (endpointCoupling π) (interpolation μ timeZero) (interpolation ν timeOne) ∧
      (∀ t : Time, interpolation π (halfTime t) = interpolation μ t) ∧
      (∀ t : Time, interpolation π (rightTime t) = interpolation ν t) ∧
      π.map halfCurve = μ ∧ π.map rightCurve = ν := by
  obtain ⟨q,hqp,hq0,hq1⟩ := exists_joinable_gluing μ ν hpush
  let := hqp
  have hfm : Measurable (fun p : Joinable X => p.1.1) := measurable_fst.comp measurable_subtype_coe
  have hsm : Measurable (fun p : Joinable X => p.1.2) := measurable_snd.comp measurable_subtype_coe
  have hjm : Measurable (joinMap (X := X)) := lipschitz_joinMap.continuous.measurable
  let π := q.map joinMap
  let : IsProbabilityMeasure π := inferInstance
  have hleft (t : Time) : interpolation π (halfTime t) = interpolation μ t := by
    change (q.map joinMap).map _ = _
    rw [Measure.map_map (continuous_eval_const _).measurable hjm, ← hq0]
    rw [interpolation,Measure.map_map (continuous_eval_const t).measurable hfm]
    congr 1; funext p; exact joinCurve_halfTime _ _ _ t
  have hright (t : Time) : interpolation π (rightTime t) = interpolation ν t := by
    change (q.map joinMap).map _ = _
    rw [Measure.map_map (continuous_eval_const _).measurable hjm, ← hq1]
    rw [interpolation,Measure.map_map (continuous_eval_const t).measurable hsm]
    congr 1; funext p; exact joinCurve_rightTime _ _ _ t
  have hcouple : IsCoupling (endpointCoupling π) (interpolation μ timeZero) (interpolation ν timeOne) := by
    convert endpointCoupling_couples π using 1
    · simpa only [halfTime_zero] using (hleft timeZero).symm
    · simpa only [rightTime_one] using (hright timeOne).symm
  let x : Joinable X → X := fun p => p.1.1 timeZero
  let y : Joinable X → X := fun p => p.1.1 timeOne
  let z : Joinable X → X := fun p => p.1.2 timeOne
  have hx : Integrable (fun p => dist (x p) (y p)^2) q := by
    have hi : Integrable (fun γ => dist (γ timeZero) (γ timeOne)^2) (q.map (fun p => p.1.1)) := by rwa [hq0]
    exact hi.comp_aemeasurable hfm.aemeasurable
  have hy : Integrable (fun p => dist (y p) (z p)^2) q := by
    have hi : Integrable (fun γ => dist (γ timeZero) (γ timeOne)^2) (q.map (fun p => p.1.2)) := by rwa [hq1]
    apply (hi.comp_aemeasurable hsm.aemeasurable).congr
    exact ae_of_all _ fun p => by dsimp only [Function.comp_def,y,z]; rw [p.2]
  have htw : Integrable (fun p => 2*(dist (x p) (y p)^2+dist (y p) (z p)^2)) q := (hx.add hy).const_mul 2
  have hle : ∀ p : Joinable X, dist (x p) (z p)^2 ≤ 2*(dist (x p) (y p)^2+dist (y p) (z p)^2) := by
    intro p
    have ht := dist_triangle (x p) (y p) (z p)
    have hd := dist_nonneg (x := x p) (y := z p)
    nlinarith [sq_nonneg (dist (x p) (y p)-dist (y p) (z p))]
  have hz : Integrable (fun p => dist (x p) (z p)^2) q := by
    apply htw.mono' (((continuous_eval_const timeZero).measurable.comp hfm).dist
      ((continuous_eval_const timeOne).measurable.comp hsm) |>.pow_const 2).aestronglyMeasurable
    exact ae_of_all _ fun p => by rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]; exact hle p
  have hIπ : Integrable (fun γ => dist (γ timeZero) (γ timeOne)^2) π := by
    apply (integrable_map_measure plan_energy_measurable.aestronglyMeasurable hjm.aemeasurable).mpr
    simpa only [Function.comp_def,joinMap,joinCurve_zero,joinCurve_one] using hz
  have heπ : planEnergy π = ∫ p, dist (x p) (z p)^2 ∂q := by
    rw [planEnergy,integral_map hjm.aemeasurable plan_energy_measurable.aestronglyMeasurable]
    simp only [joinMap,joinCurve_zero,joinCurve_one,x,z]
  have heμ : planEnergy μ = ∫ p, dist (x p) (y p)^2 ∂q := by
    rw [planEnergy,← hq0,integral_map hfm.aemeasurable plan_energy_measurable.aestronglyMeasurable]
  have heν : planEnergy ν = ∫ p, dist (y p) (z p)^2 ∂q := by
    rw [planEnergy,← hq1,integral_map hsm.aemeasurable plan_energy_measurable.aestronglyMeasurable]
    apply integral_congr_ae
    exact ae_of_all _ fun p => by dsimp only [y,z]; rw [p.2]
  have hoptLE : planEnergy ρ ≤ planEnergy π := by
    have H := hρ.2 (endpointCoupling π) hcouple
    rw [planCost_eq_ofReal_energy hIρ,planCost_eq_ofReal_energy hIπ] at H
    exact (ENNReal.ofReal_le_ofReal_iff (planEnergy_nonneg π)).mp H
  have hePoint := quadratic_triangle_rigidity x y z hx hy hz (by
    rw [heμ,heν] at hbudget
    rw [heπ] at hoptLE
    exact hbudget.trans hoptLE)
  have hg0 : ∀ᵐ p ∂q, IsGeodesic p.1.1 := by
    apply (ae_map_iff hfm.aemeasurable isClosed_isGeodesic.measurableSet).mp
    rwa [hq0]
  have hg1 : ∀ᵐ p ∂q, IsGeodesic p.1.2 := by
    apply (ae_map_iff hsm.aemeasurable isClosed_isGeodesic.measurableSet).mp
    rwa [hq1]
  have hgπ : ∀ᵐ γ ∂π, IsGeodesic γ := by
    apply (ae_map_iff hjm.aemeasurable isClosed_isGeodesic.measurableSet).mpr
    filter_upwards [hg0,hg1,hePoint] with p h0 h1 hp
    apply joinCurve_isGeodesic p.2 h0 h1 _ hp.2
    exact hp.1.trans (congrArg (fun a => dist a (p.1.2 timeOne)) p.2)
  have hEnergyLE : planEnergy π ≤ planEnergy ρ := by
    have H := integral_mono hz htw hle
    rw [integral_const_mul,integral_add hx hy,← heμ,← heν,← heπ] at H
    exact H.trans hbudget
  refine ⟨π,inferInstance,hgπ,⟨hcouple,?_⟩,hleft,hright,?_,?_⟩
  · intro r hr
    apply le_trans _ (hρ.2 r hr)
    rw [planCost_eq_ofReal_energy hIπ,planCost_eq_ofReal_energy hIρ]
    exact ENNReal.ofReal_le_ofReal hEnergyLE
  · change (q.map joinMap).map halfCurve = μ
    rw [Measure.map_map continuous_halfCurve.measurable hjm, ← hq0]
    congr 1; funext p; exact halfCurve_joinCurve _ _ _
  · change (q.map joinMap).map rightCurve = ν
    rw [Measure.map_map continuous_rightCurve.measurable hjm, ← hq1]
    congr 1; funext p; exact rightCurve_joinCurve _ _ _

end WeakHessian
end

end OAI
