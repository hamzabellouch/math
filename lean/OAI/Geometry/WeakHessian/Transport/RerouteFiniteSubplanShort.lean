import Mathlib
import OAI.Geometry.WeakHessian.Measure.OptimalTimeLawSupported
import OAI.Geometry.WeakHessian.Transport.OptimalPlansShort

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

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

lemma CurvatureDimension.reroute_finite_subplan_short {m : Measure X} [SigmaFinite m]
    {K N : ℝ} (hN : 1 < N) (hcd : CurvatureDimension m K N)
    (θ : Measure (Curve X)) [IsFiniteMeasure θ] (hq : θ univ ≠ 0)
    (o : X) {R : ℝ} (_ : 0 ≤ R) (D : ℝ≥0)
    (hshort : OptimalPlansShort (interpolation ((θ univ)⁻¹ • θ) timeZero)
      (interpolation ((θ univ)⁻¹ • θ) timeOne) D)
    (hb : ∀ᵐ γ ∂θ, dist (γ timeZero) o ≤ R ∧ dist (γ timeOne) o ≤ R)
    {C : ℝ≥0∞} (hd₀ : interpolation θ timeZero ≤ C • m)
    (hd₁ : interpolation θ timeOne ≤ C • m) :
    ∃ ξ : Measure (Curve X), IsFiniteMeasure ξ ∧ ξ univ = θ univ ∧
      (∀ᵐ γ ∂ξ, IsGeodesic γ) ∧
      interpolation ξ timeZero = interpolation θ timeZero ∧
      interpolation ξ timeOne = interpolation θ timeOne ∧
      QuadraticTransportCost (endpointCoupling ξ) ≤ QuadraticTransportCost (endpointCoupling θ) ∧
      ∀ B : Set X, MeasurableSet B → interpolation ξ timeHalf Bᶜ = 0 →
        ((2:ℝ≥0∞)*midpointTauLower K N D)^N / ((θ univ)⁻¹*C) ≤ m B := by
  let q := θ univ
  have hqt : q ≠ ∞ := measure_ne_top _ _
  let θ' : Measure (Curve X) := q⁻¹ • θ
  have hp : IsProbabilityMeasure θ' := by
    constructor
    change q⁻¹*θ univ = 1
    exact ENNReal.inv_mul_cancel hq hqt
  let := hp
  have hcanc : q • θ' = θ := by
    change q • (q⁻¹ • θ) = θ
    rw [smul_smul,ENNReal.mul_inv_cancel hq hqt,one_smul]
  let μ₀ := interpolation θ' timeZero
  let μ₁ := interpolation θ' timeOne
  let : IsProbabilityMeasure μ₀ := interpolation_probability θ' timeZero
  let : IsProbabilityMeasure μ₁ := interpolation_probability θ' timeOne
  have he (t : Time) : interpolation θ' t = q⁻¹ • interpolation θ t :=
    Measure.map_smul _ (continuous_eval_const t).measurable.aemeasurable
  have hd0 : μ₀ ≤ (q⁻¹*C) • m := by
    dsimp only [μ₀]
    rw [he,← smul_smul]
    exact smul_le_smul_left _ hd₀
  have hd1 : μ₁ ≤ (q⁻¹*C) • m := by
    dsimp only [μ₁]
    rw [he,← smul_smul]
    exact smul_le_smul_left _ hd₁
  have hac0 : μ₀ ≪ m := (Measure.absolutelyContinuous_of_le hd0).trans
    (Measure.AbsolutelyContinuous.rfl.smul_left _)
  have hac1 : μ₁ ≪ m := (Measure.absolutelyContinuous_of_le hd1).trans
    (Measure.AbsolutelyContinuous.rfl.smul_left _)
  have hb' : ∀ᵐ γ ∂θ', dist (γ timeZero) o ≤ R ∧ dist (γ timeOne) o ≤ R :=
    (Measure.AbsolutelyContinuous.rfl.smul_left _).ae_le hb
  have hb0 : ∀ᵐ x ∂μ₀, dist x o ≤ R :=
    (ae_map_iff (continuous_eval_const timeZero).measurable.aemeasurable
      (measurableSet_le (continuous_id.dist continuous_const).measurable measurable_const)).mpr
      (hb'.mono fun _ h => h.1)
  have hb1 : ∀ᵐ x ∂μ₁, dist x o ≤ R :=
    (ae_map_iff (continuous_eval_const timeOne).measurable.aemeasurable
      (measurableSet_le (continuous_id.dist continuous_const).measurable measurable_const)).mpr
      (hb'.mono fun _ h => h.2)
  obtain ⟨π,hπ,hgeo,hopt,hent⟩ := hcd μ₀ μ₁ inferInstance inferInstance
    (hasSecondMoment_of_ae_dist_le o R hb0) (hasSecondMoment_of_ae_dist_le o R hb1) hac0 hac1
  let := hπ
  obtain ⟨he0,he1⟩ := hopt.1.interpolation_endpoints
  have hlen : ∀ᵐ γ ∂π, dist (γ timeZero) (γ timeOne) ≤ D := hshort π hπ hgeo hopt
  let ξ := q • π
  have hξmass : ξ univ = θ univ := by simp [ξ,q]
  have hξfin : IsFiniteMeasure ξ := ⟨hξmass ▸ measure_lt_top θ univ⟩
  have hξend (t : Time) (ht : interpolation π t = interpolation θ' t) :
      interpolation ξ t = interpolation θ t := by
    change (q • π).map _ = _
    rw [Measure.map_smul _ (continuous_eval_const t).measurable.aemeasurable]
    change q • interpolation π t = _
    rw [ht]
    change q • θ'.map (fun γ => γ t) = θ.map (fun γ => γ t)
    rw [← Measure.map_smul _ (continuous_eval_const t).measurable.aemeasurable,hcanc]
  refine ⟨ξ,hξfin,hξmass,(Measure.AbsolutelyContinuous.rfl.smul_left _).ae_le hgeo,
    hξend timeZero he0,hξend timeOne he1,?_,?_⟩
  · have H := mul_le_mul' (le_refl q) (hopt.2 (endpointCoupling θ') (endpointCoupling_couples θ'))
    change q*QuadraticTransportCost (endpointCoupling π) ≤ q*QuadraticTransportCost (endpointCoupling θ') at H
    have hs (η : Measure (Curve X)) : QuadraticTransportCost (endpointCoupling (q • η)) =
        q*QuadraticTransportCost (endpointCoupling η) := by
      unfold QuadraticTransportCost endpointCoupling
      rw [Measure.map_smul q ((continuous_eval_const timeZero).measurable.prodMk
          (continuous_eval_const timeOne).measurable).aemeasurable,
        lintegral_smul_measure,smul_eq_mul]
    rw [← hs π,← hs θ',hcanc] at H
    exact H
  · intro B hB hs
    have hs' : interpolation π timeHalf Bᶜ = 0 := by
      change (q • π).map _ Bᶜ = 0 at hs
      rw [Measure.map_smul _ (continuous_eval_const timeHalf).measurable.aemeasurable,
        Measure.smul_apply,smul_eq_mul] at hs
      exact (mul_eq_zero.mp hs).resolve_left hq
    apply cd_midpoint_support_lower hN D.property hopt.1
      (hac0.ae_le (rnDeriv_le_of_le_smul hd0))
      (hac1.ae_le (rnDeriv_le_of_le_smul hd1)) hlen ?_ hB hs'
    simpa only [timeHalf, show (1 : ℝ)-1/2 = 1/2 by norm_num] using hent N le_rfl timeHalf

lemma CurvatureDimension.reroute_midpoint_restriction_short
    [SecondCountableTopology X] {m : Measure X} [SigmaFinite m]
    {K N : ℝ} (hN : 1 < N) (hcd : CurvatureDimension m K N)
    {μ₀ μ₁ μ : ProbabilityMeasure X} (hμ : μ ∈ optimalTimeLaws μ₀ μ₁ timeHalf)
    (o : X) (R : ℝ≥0)
    (hb₀ : (μ₀:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (hb₁ : (μ₁:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (D : ℝ≥0) (hshort : OptimalPlansShort (μ₀:Measure X) (μ₁:Measure X) D)
    {C : ℝ≥0∞} (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hd₀ : (μ₀:Measure X) ≤ C • m) (hd₁ : (μ₁:Measure X) ≤ C • m)
    {A : Set X} (hA : MeasurableSet A) (hq : (μ:Measure X) A ≠ 0)
    {d : ℝ≥0∞} (hd : d ≠ 0) (hdt : d ≠ ∞) (hd1 : d ≤ 1) :
    ∃ (β : Measure X) (η : ProbabilityMeasure X), IsFiniteMeasure β ∧
      β univ = d*(μ:Measure X) A ∧ η ∈ optimalTimeLaws μ₀ μ₁ timeHalf ∧
      (η:Measure X) = (μ:Measure X)-d • (μ:Measure X).restrict A+β ∧
      β (Metric.closedBall o (3*(R:ℝ)))ᶜ = 0 ∧
      ∀ B : Set X, MeasurableSet B → β Bᶜ = 0 →
        ((2:ℝ≥0∞)*midpointTauLower K N D)^N*(μ:Measure X) A/C ≤ m B := by
  obtain ⟨π,hgeo,hopt,hμeq⟩ := hμ
  have heμ : (μ:Measure X) = interpolation (π:Measure (Curve X)) timeHalf :=
    congrArg Subtype.val hμeq
  let θ : Measure (Curve X) := d • (π:Measure (Curve X)).restrict ((fun γ => γ timeHalf) ⁻¹' A)
  have hscale : d • (π:Measure (Curve X)) ≤ (π:Measure (Curve X)) := by
    intro S
    change d*(π:Measure (Curve X)) S ≤ (π:Measure (Curve X)) S
    simpa using mul_le_mul' hd1 (le_refl ((π:Measure (Curve X)) S))
  have hθ : θ ≤ (π:Measure (Curve X)) :=
    (smul_le_smul_left d Measure.restrict_le_self).trans hscale
  let : IsFiniteMeasure θ := isFiniteMeasure_of_le (π:Measure (Curve X)) hθ
  have hθmass : θ univ = d*(μ:Measure X) A := by
    rw [heμ,interpolation,Measure.map_apply (continuous_eval_const timeHalf).measurable hA]
    simp [θ]
  have hθ0 : θ univ ≠ 0 := by rw [hθmass]; exact mul_ne_zero hd hq
  have hθb : ∀ᵐ γ ∂θ, dist (γ timeZero) o ≤ R ∧ dist (γ timeOne) o ≤ R := by
    have H := optimalPlan_supported_tube π hgeo hopt.1 hb₀ hb₁
    exact (Measure.absolutelyContinuous_of_le hθ).ae_le ((ae_iff.mpr H).mono fun _ h => h.2)
  have hθend (t : Time) : interpolation θ t ≤ d • interpolation (π:Measure (Curve X)) t := by
    dsimp only [θ,interpolation]

    rw [Measure.map_smul _ (continuous_eval_const t).measurable.aemeasurable]
    exact smul_le_smul_left d (Measure.map_mono Measure.restrict_le_self (continuous_eval_const t).measurable)
  have hde0 : interpolation θ timeZero ≤ (d*C) • m := by
    calc
      _ ≤ d • interpolation (π:Measure (Curve X)) timeZero := hθend _
      _ = d • (μ₀:Measure X) := by rw [hopt.1.interpolation_endpoints.1]
      _ ≤ d • (C • m) := smul_le_smul_left d hd₀
      _ = _ := smul_smul _ _ _
  have hde1 : interpolation θ timeOne ≤ (d*C) • m := by
    calc
      _ ≤ d • interpolation (π:Measure (Curve X)) timeOne := hθend _
      _ = d • (μ₁:Measure X) := by rw [hopt.1.interpolation_endpoints.2]
      _ ≤ d • (C • m) := smul_le_smul_left d hd₁
      _ = _ := smul_smul _ _ _
  obtain ⟨ξ,hξfin,hξmass,hξgeo,hξ0,hξ1,hξcost,hξspread⟩ :=
    hcd.reroute_finite_subplan_short hN θ hθ0 o R.property D
      (hshort.subplan (π:Measure (Curve X)) hgeo hopt θ hθ hθ0) hθb hde0 hde1
  let := hξfin
  let ω := (π:Measure (Curve X))-θ+ξ
  let : IsProbabilityMeasure ω := replacement_probability _ _ _ hθ hξmass
  let ηπ : ProbabilityMeasure (Curve X) := ⟨ω,inferInstance⟩
  let η := ηπ.map (fun γ => γ timeHalf)
  let β := interpolation ξ timeHalf
  have hβfin : IsFiniteMeasure β := Measure.isFiniteMeasure_map ξ _
  have hξb0 : interpolation ξ timeZero (Metric.closedBall o R)ᶜ = 0 := by
    rw [hξ0]
    apply le_antisymm _ bot_le
    calc
      _ ≤ d*interpolation (π:Measure (Curve X)) timeZero (Metric.closedBall o R)ᶜ := hθend _ _
      _ = 0 := by rw [hopt.1.interpolation_endpoints.1,hb₀,mul_zero]
  have hξb1 : interpolation ξ timeOne (Metric.closedBall o R)ᶜ = 0 := by
    rw [hξ1]
    apply le_antisymm _ bot_le
    calc
      _ ≤ d*interpolation (π:Measure (Curve X)) timeOne (Metric.closedBall o R)ᶜ := hθend _ _
      _ = 0 := by rw [hopt.1.interpolation_endpoints.2,hb₁,mul_zero]
  refine ⟨β,η,hβfin,?_,?_,?_,geodesic_plan_supported_ball ξ hξgeo o R hξb0 hξb1 timeHalf,?_⟩
  · dsimp [β,interpolation]
    rw [Measure.map_apply_of_aemeasurable (continuous_eval_const timeHalf).measurable.aemeasurable MeasurableSet.univ]
    simpa only [preimage_univ] using hξmass.trans hθmass
  · exact ⟨ηπ,geodesic_plan_reroute hgeo hξgeo,hopt.reroute_plan hθ hξ0 hξ1 hξcost,rfl⟩
  · change (ω.map (fun γ => γ timeHalf)) = _
    rw [show ω = (π:Measure (Curve X))-θ+ξ from rfl,
      Measure.map_add _ _ (continuous_eval_const timeHalf).measurable,
      map_sub_of_le _ _ hθ (continuous_eval_const timeHalf).measurable]
    have heθ : interpolation θ timeHalf = d • (μ:Measure X).restrict A := by
      change Measure.map (fun γ : Curve X => γ timeHalf) (d • (π:Measure (Curve X)).restrict _) = _
      rw [Measure.map_smul _ (continuous_eval_const timeHalf).measurable.aemeasurable]
      rw [← interpolation,interpolation_restricted _ _ hA,← heμ]
    change interpolation (π:Measure (Curve X)) timeHalf - interpolation θ timeHalf + β = _
    rw [heθ,heμ]
  · intro B hB hβB
    have H := hξspread B hB hβB
    rw [hθmass,scaled_CD_spreading_constant hq (measure_ne_top _ _) hC hCt hd hdt] at H
    exact H

theorem CurvatureDimension.exists_bounded_midpoint_preserving_caps_short
    [SecondCountableTopology X] [ProperSpace X] {m : Measure X} [SigmaFinite m]
    {K N : ℝ} (hN : 1 < N) (hcd : CurvatureDimension m K N)
    (hfin : FiniteOnBoundedSets m) {μ₀ μ₁ : ProbabilityMeasure X}
    (o : X) (R : ℝ≥0)
    (hb₀ : (μ₀:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (hb₁ : (μ₁:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (D : ℝ≥0) (hshort : OptimalPlansShort (μ₀:Measure X) (μ₁:Measure X) D)
    {C : ℝ≥0∞} (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hd₀ : (μ₀:Measure X) ≤ C • m) (hd₁ : (μ₁:Measure X) ≤ C • m)
    {I : Type*} (W : I → Measure X)
    (hW : ∀ i, W i ≤ (C/((2:ℝ≥0∞)*midpointTauLower K N D)^N) •
      m.restrict (Metric.closedBall o (3*(R:ℝ))))
    (μref : ProbabilityMeasure X) (href : μref ∈ optimalTimeLaws μ₀ μ₁ timeHalf)
    {b : ℝ≥0∞} (hb : 1 < b) (hbt : b ≠ ∞) :
    ∃ μ ∈ optimalTimeLaws μ₀ μ₁ timeHalf,
      (μ:Measure X) ≤ (b*C/((2:ℝ≥0∞)*midpointTauLower K N D)^N) •
        m.restrict (Metric.closedBall o (3*(R:ℝ))) ∧
      ∀ i, cappedExcess (W i) μ ≤ cappedExcess (W i) μref := by
  let a : ℝ≥0∞ := ((2:ℝ≥0∞)*midpointTauLower K N D)^N
  have ha0 : a ≠ 0 := (ENNReal.rpow_pos
    (ENNReal.mul_pos_iff.mpr ⟨by norm_num,midpointTauLower_pos _ _ _⟩)
    (ENNReal.mul_ne_top (by simp) (midpointTauLower_ne_top hN))).ne'
  have hat : a ≠ ∞ := ENNReal.rpow_ne_top_of_ne_zero
    (mul_ne_zero (by norm_num) (midpointTauLower_pos _ _ _).ne')
    (ENNReal.mul_ne_top (by simp) (midpointTauLower_ne_top hN))
  let Q := Metric.closedBall o (3*(R:ℝ))
  have hQ : MeasurableSet Q := Metric.isClosed_closedBall.measurableSet
  let ν := (b*C/a) • m.restrict Q
  have hνfin : IsFiniteMeasure ν := by
    constructor
    change (b*C/a)*(m.restrict Q) univ < ∞
    rw [Measure.restrict_apply_univ]
    exact ENNReal.mul_lt_top
      (lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top (ENNReal.mul_ne_top hbt hCt) (ENNReal.inv_ne_top.mpr ha0)))
      (hfin Q Metric.isBounded_closedBall)
  let := hνfin
  have hWV (i : I) : W i ≤ ν := by
    apply (hW i).trans
    have hc : C/a ≤ b*C/a := by
      apply mul_le_mul' _ le_rfl
      simpa only [one_mul] using mul_le_mul' hb.le (le_refl C)
    intro A
    exact mul_le_mul' hc (le_refl ((m.restrict Q) A))
  let S : Set (ProbabilityMeasure X) := optimalTimeLaws μ₀ μ₁ timeHalf ∩
    {μ | ∀ i, cappedExcess (W i) μ ≤ cappedExcess (W i) μref}
  have hSc : IsCompact S := by
    apply (isCompact_optimalTimeLaws o R hb₀ hb₁ timeHalf).inter_right
    convert isClosed_iInter (fun i =>
      (cappedExcess_lowerSemicontinuous (W i)).isClosed_preimage (cappedExcess (W i) μref)) using 1
    ext μ
    simp
  obtain ⟨μ,hμ,hdμ⟩ : ∃ μ ∈ S, (μ:Measure X) ≤ ν := by
    apply exists_dominated_of_compact_rerouting (S := S) ν ⟨μref,href,fun _ => le_rfl⟩ hSc
    intro μ hμS P hP hsur
    have hμ := hμS.1
    let δ := (μ:Measure X)-ν
    let : IsFiniteMeasure δ := isFiniteMeasure_of_le (μ:Measure X) Measure.sub_le
    have hmass : (μ:Measure X) P ≠ 0 := ne_of_gt (hsur.trans_le hP.surplus_le_mass)
    have hb0 : b ≠ 0 := (zero_lt_one.trans hb).ne'
    have hsmall : (μ:Measure X) P/b < (μ:Measure X) P := by
      apply (ENNReal.div_lt_iff (Or.inl hb0) (Or.inl hbt)).mpr
      simpa only [one_mul,mul_comm] using ENNReal.mul_lt_mul_left hmass (measure_ne_top _ _) hb
    obtain ⟨A,n,hA,hAP,hn,hAmass,hAdom⟩ := exists_bounded_rn_subrestriction
      (μ:Measure X) δ hP.measurableSet hP.mass_ac hsmall
    have hn0 : (n:ℝ≥0∞) ≠ 0 := by exact_mod_cast hn.ne'
    have hnt : (n:ℝ≥0∞) ≠ ∞ := by simp
    let d : ℝ≥0∞ := (n:ℝ≥0∞)⁻¹
    have hd : d ≠ 0 := ENNReal.inv_ne_zero.mpr hnt
    have hdt : d ≠ ∞ := ENNReal.inv_ne_top.mpr hn0
    have hd1 : d ≤ 1 := ENNReal.inv_le_one.mpr (by exact_mod_cast hn)
    have hA0 : (μ:Measure X) A ≠ 0 := ne_of_gt (bot_le.trans_lt hAmass)
    obtain ⟨β,η,hβfin,hβmass,hη,hηeq,hβQ,hspread⟩ :=
      hcd.reroute_midpoint_restriction_short hN hμ o R hb₀ hb₁ D hshort hC hCt hd₀ hd₁ hA hA0 hd hdt hd1
    let ρ := d • (μ:Measure X).restrict A
    have hρ : ρ ≤ δ := by
      calc
        _ ≤ d • ((n:ℝ≥0∞) • δ) := smul_le_smul_left d hAdom
        _ = δ := by rw [smul_smul,show d*(n:ℝ≥0∞)=1 from ENNReal.inv_mul_cancel hn0 hnt,one_smul]
    have hηS : η ∈ S := by
      refine ⟨hη,fun i => ?_⟩
      let : IsFiniteMeasure (W i) := isFiniteMeasure_of_le ν (hWV i)
      let := hβfin
      have hρW : ρ ≤ (μ:Measure X)-W i := by
        apply hρ.trans
        apply Measure.sub_le_of_le_add
        exact (measure_le_sub_add (μ:Measure X) (W i)).trans (add_le_add le_rfl (hWV i))
      apply (cappedExcess_relocation_le (W i) μ η ρ β hρW _ hηeq).trans (hμS.2 i)
      simpa [ρ,Measure.smul_apply] using hβmass
    refine ⟨ρ,β,η,hβfin,hρ,?_,hηS,hηeq,?_⟩
    · simpa [ρ,Measure.smul_apply] using hβmass
    · intro B hB hβB
      have hsupport : β (B ∩ Q)ᶜ = 0 := by
        rw [compl_inter]
        exact measure_union_null hβB hβQ
      have H := hspread (B ∩ Q) (hB.inter hQ) hsupport
      calc
        ν P + ((μ:Measure X)-ν) univ = (μ:Measure X) P := hP.exact_mass.symm
        _ ≤ b*(μ:Measure X) A := by
          have H' := mul_le_mul' hAmass.le (le_refl b)
          rw [ENNReal.div_mul_cancel hb0 hbt] at H'
          simpa only [mul_comm] using H'
        _ = (b*C/a)*(a*(μ:Measure X) A/C) := (CD_cap_support_cancel ha0 hat hC hCt).symm
        _ ≤ (b*C/a)*m (B ∩ Q) := mul_le_mul' le_rfl H
        _ = ν B := by simp only [ν,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply hB]
  exact ⟨μ,hμ.1,hdμ,hμ.2⟩

theorem CurvatureDimension.exists_sharp_midpoint_preserving_caps_short
    [SecondCountableTopology X] [ProperSpace X] {m : Measure X} [SigmaFinite m]
    {K N : ℝ} (hN : 1 < N) (hcd : CurvatureDimension m K N)
    (hfin : FiniteOnBoundedSets m) {μ₀ μ₁ : ProbabilityMeasure X}
    (o : X) (R : ℝ≥0)
    (hb₀ : (μ₀:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (hb₁ : (μ₁:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (D : ℝ≥0) (hshort : OptimalPlansShort (μ₀:Measure X) (μ₁:Measure X) D)
    {C : ℝ≥0∞} (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hd₀ : (μ₀:Measure X) ≤ C • m) (hd₁ : (μ₁:Measure X) ≤ C • m)
    {I : Type*} (W : I → Measure X)
    (hW : ∀ i, W i ≤ (C/((2:ℝ≥0∞)*midpointTauLower K N D)^N) •
      m.restrict (Metric.closedBall o (3*(R:ℝ))))
    (μref : ProbabilityMeasure X) (href : μref ∈ optimalTimeLaws μ₀ μ₁ timeHalf) :
    ∃ μ ∈ optimalTimeLaws μ₀ μ₁ timeHalf,
      (μ:Measure X) ≤ (C/((2:ℝ≥0∞)*midpointTauLower K N D)^N) •
        m.restrict (Metric.closedBall o (3*(R:ℝ))) ∧
      ∀ i, cappedExcess (W i) μ ≤ cappedExcess (W i) μref := by
  let a : ℝ≥0∞ := ((2:ℝ≥0∞)*midpointTauLower K N D)^N
  have ha0 : a ≠ 0 := (ENNReal.rpow_pos
    (ENNReal.mul_pos_iff.mpr ⟨by norm_num,midpointTauLower_pos _ _ _⟩)
    (ENNReal.mul_ne_top (by simp) (midpointTauLower_ne_top hN))).ne'
  let ν := (C/a) • m.restrict (Metric.closedBall o (3*(R:ℝ)))
  have hνfin : IsFiniteMeasure ν := by
    constructor
    change (C/a)*(m.restrict (Metric.closedBall o (3*(R:ℝ)))) univ < ∞
    rw [Measure.restrict_apply_univ]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr (ENNReal.div_ne_top hCt ha0))
      (hfin _ Metric.isBounded_closedBall)
  let := hνfin
  let S : Set (ProbabilityMeasure X) := optimalTimeLaws μ₀ μ₁ timeHalf ∩
    {μ | ∀ i, cappedExcess (W i) μ ≤ cappedExcess (W i) μref}
  have hSc : IsCompact S := by
    apply (isCompact_optimalTimeLaws o R hb₀ hb₁ timeHalf).inter_right
    convert isClosed_iInter (fun i =>
      (cappedExcess_lowerSemicontinuous (W i)).isClosed_preimage (cappedExcess (W i) μref)) using 1
    ext μ
    simp
  obtain ⟨μ,hμ,hdμ⟩ : ∃ μ ∈ S, (μ:Measure X) ≤ ν := by
    apply exists_dominated_of_approximations ν hSc
    intro b hb hbt
    obtain ⟨μ,hμ,hμdom,hcaps⟩ := hcd.exists_bounded_midpoint_preserving_caps_short
      hN hfin o R hb₀ hb₁ D hshort hC hCt hd₀ hd₁ W hW μref href hb hbt
    refine ⟨μ,⟨hμ,hcaps⟩,?_⟩
    simpa only [ν,smul_smul,div_eq_mul_inv,mul_assoc] using hμdom
  exact ⟨μ,hμ.1,hdμ,hμ.2⟩

theorem CurvatureDimension.exists_sharp_midpoint_above_lower_short
    [SecondCountableTopology X] [ProperSpace X] {m : Measure X} [SigmaFinite m]
    {K N : ℝ} (hN : 1 < N) (hcd : CurvatureDimension m K N)
    (hfin : FiniteOnBoundedSets m) {μ₀ μ₁ : ProbabilityMeasure X}
    (o : X) (R : ℝ≥0)
    (hb₀ : (μ₀:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (hb₁ : (μ₁:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (D : ℝ≥0) (hshort : OptimalPlansShort (μ₀:Measure X) (μ₁:Measure X) D)
    {C : ℝ≥0∞} (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hd₀ : (μ₀:Measure X) ≤ C • m) (hd₁ : (μ₁:Measure X) ≤ C • m)
    (κ : Measure X)
    (hκcap : κ ≤ (C/((2:ℝ≥0∞)*midpointTauLower K N D)^N) •
      m.restrict (Metric.closedBall o (3*(R:ℝ))))
    (μref : ProbabilityMeasure X) (href : μref ∈ optimalTimeLaws μ₀ μ₁ timeHalf)
    (hκref : κ ≤ (μref:Measure X)) :
    ∃ μ ∈ optimalTimeLaws μ₀ μ₁ timeHalf,
      (μ:Measure X) ≤ (C/((2:ℝ≥0∞)*midpointTauLower K N D)^N) •
        m.restrict (Metric.closedBall o (3*(R:ℝ))) ∧ κ ≤ (μ:Measure X) := by
  let : IsFiniteMeasure κ := isFiniteMeasure_of_le (μref:Measure X) hκref
  obtain ⟨μ,hμ,hdμ,hcaps⟩ := hcd.exists_sharp_midpoint_preserving_caps_short
    hN hfin o R hb₀ hb₁ D hshort hC hCt hd₀ hd₁ (fun _ : Unit => κ) (fun _ => hκcap) μref href
  exact ⟨μ,hμ,hdμ,lower_dominance_of_cap_le κ μref μ hκref (hcaps ())⟩

theorem CurvatureDimension.exists_entropy_improving_sharp_midpoint_short
    [SecondCountableTopology X] [ProperSpace X] {m : Measure X} [SigmaFinite m]
    {K N : ℝ} (hN : 1 < N) (hcd : CurvatureDimension m K N)
    (hfin : FiniteOnBoundedSets m) {μ₀ μ₁ : ProbabilityMeasure X}
    (o : X) (R : ℝ≥0)
    (hb₀ : (μ₀:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (hb₁ : (μ₁:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (D : ℝ≥0) (hshort : OptimalPlansShort (μ₀:Measure X) (μ₁:Measure X) D)
    {C : ℝ≥0∞} (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hd₀ : (μ₀:Measure X) ≤ C • m) (hd₁ : (μ₁:Measure X) ≤ C • m)
    (μref : ProbabilityMeasure X) (href : μref ∈ optimalTimeLaws μ₀ μ₁ timeHalf)
    (hEref : FiniteEntropy m (μref:Measure X)) :
    ∃ μ ∈ optimalTimeLaws μ₀ μ₁ timeHalf,
      (μ:Measure X) ≤ (C/((2:ℝ≥0∞)*midpointTauLower K N D)^N) •
        m.restrict (Metric.closedBall o (3*(R:ℝ))) ∧
      FiniteEntropy m (μ:Measure X) ∧ entropyReal m (μ:Measure X) ≤ entropyReal m (μref:Measure X) := by
  let a : ℝ≥0∞ := ((2:ℝ≥0∞)*midpointTauLower K N D)^N
  have ha0 : a ≠ 0 := (ENNReal.rpow_pos
    (ENNReal.mul_pos_iff.mpr ⟨by norm_num,midpointTauLower_pos _ _ _⟩)
    (ENNReal.mul_ne_top (by simp) (midpointTauLower_ne_top hN))).ne'
  have hat : a ≠ ∞ := ENNReal.rpow_ne_top_of_ne_zero
    (mul_ne_zero (by norm_num) (midpointTauLower_pos _ _ _).ne')
    (ENNReal.mul_ne_top (by simp) (midpointTauLower_ne_top hN))
  let B := C/a
  have hB : B ≠ 0 := ENNReal.div_ne_zero.mpr ⟨hC,hat⟩
  have hBt : B ≠ ∞ := ENNReal.div_ne_top hCt ha0
  let Q := Metric.closedBall o (3*(R:ℝ))
  have hQ : MeasurableSet Q := Metric.isClosed_closedBall.measurableSet
  let : IsFiniteMeasure (m.restrict Q) := ⟨by simpa only [Measure.restrict_apply_univ] using hfin Q Metric.isBounded_closedBall⟩
  have hsref : ∀ᵐ x ∂(μref:Measure X), x ∈ Q :=
    ae_iff.mpr (optimalTimeLaw_supported_ball href o R hb₀ hb₁)
  have hErefQ := (finiteEntropy_restrict_reference_iff hQ hsref).mpr hEref
  let κ := (m.restrict Q).withDensity (fun x => min ((μref:Measure X).rnDeriv (m.restrict Q) x) B)
  have hκcap : κ ≤ B • m.restrict Q := by
    rw [← withDensity_const]
    exact withDensity_mono (ae_of_all _ fun x => min_le_right _ _)
  have hκref : κ ≤ (μref:Measure X) := by
    rw [← Measure.withDensity_rnDeriv_eq (μref:Measure X) (m.restrict Q) hErefQ.1]
    exact withDensity_mono (ae_of_all _ fun x => min_le_left _ _)
  obtain ⟨μ,hμ,hdμ,hκμ⟩ := hcd.exists_sharp_midpoint_above_lower_short hN hfin o R hb₀ hb₁
    D hshort hC hCt hd₀ hd₁ κ hκcap μref href hκref
  obtain ⟨hEμQ,hent⟩ := entropyReal_le_of_density_capping (μref:Measure X) (μ:Measure X)
    hErefQ hB hBt hdμ hκμ
  have hsμ : ∀ᵐ x ∂(μ:Measure X), x ∈ Q :=
    ae_iff.mpr (optimalTimeLaw_supported_ball hμ o R hb₀ hb₁)
  have hEμ := (finiteEntropy_restrict_reference_iff hQ hsμ).mp hEμQ
  refine ⟨μ,hμ,hdμ,hEμ,?_⟩
  rwa [entropyReal_restrict_reference hQ hEμ.1 hsμ,
    entropyReal_restrict_reference hQ hEref.1 hsref] at hent

theorem CurvatureDimension.exists_entropy_bounded_midpoint_short
    [SecondCountableTopology X] [ProperSpace X] {m : Measure X} [SigmaFinite m]
    {K N : ℝ} (hN : 1 < N) (hcd : CurvatureDimension m K N)
    (hfin : FiniteOnBoundedSets m) (μ₀ μ₁ : ProbabilityMeasure X)
    (o : X) (R : ℝ≥0)
    (hb₀ : (μ₀:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (hb₁ : (μ₁:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (D : ℝ≥0) (hshort : OptimalPlansShort (μ₀:Measure X) (μ₁:Measure X) D)
    {C : ℝ≥0∞} (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hd₀ : (μ₀:Measure X) ≤ C • m) (hd₁ : (μ₁:Measure X) ≤ C • m)
    (hE₀ : FiniteEntropy m (μ₀:Measure X)) (hE₁ : FiniteEntropy m (μ₁:Measure X)) :
    ∃ π : ProbabilityMeasure (Curve X),
      (∀ᵐ γ ∂(π:Measure (Curve X)), IsGeodesic γ) ∧
      IsOptimalCoupling (endpointCoupling (π:Measure (Curve X))) μ₀ μ₁ ∧
      interpolation (π:Measure (Curve X)) timeHalf ≤
        (C/((2:ℝ≥0∞)*midpointTauLower K N D)^N) • m.restrict (Metric.closedBall o (3*(R:ℝ))) ∧
      FiniteEntropy m (interpolation (π:Measure (Curve X)) timeHalf) ∧
      entropyReal m (interpolation (π:Measure (Curve X)) timeHalf) ≤
        (entropyReal m (μ₀:Measure X)+entropyReal m (μ₁:Measure X))/2 -
          K/8*(∫ γ, dist (γ timeZero) (γ timeOne)^2 ∂(π:Measure (Curve X))) := by
  obtain ⟨π,hp,hg,ho,hE⟩ := cd_entropy_plan_bounded hN hcd hfin hE₀ hE₁ o R.2
    (ae_iff.mpr hb₀) (ae_iff.mpr hb₁)
  let := hp
  let πp : ProbabilityMeasure (Curve X) := ⟨π,hp⟩
  let μref : ProbabilityMeasure X := πp.map (fun γ => γ timeHalf)
  have href : μref ∈ optimalTimeLaws μ₀ μ₁ timeHalf := ⟨πp,hg,ho,rfl⟩
  obtain ⟨μ,hμ,hdμ,hEμ,hentμ⟩ := hcd.exists_entropy_improving_sharp_midpoint_short
    hN hfin o R hb₀ hb₁ D hshort hC hCt hd₀ hd₁ μref href (hE timeHalf).1
  obtain ⟨η,hgη,hoη,hμeq⟩ := hμ
  have hcost := optimal_cost_integral_eq πp η o R hg hgη ho hoη hb₀ hb₁
  have hbound := hentμ.trans (hE timeHalf).2
  rw [hμeq] at hdμ hEμ hbound
  refine ⟨η,hgη,hoη,hdμ,hEμ,?_⟩
  change entropyReal m (interpolation (η:Measure (Curve X)) timeHalf) ≤ _ at hbound
  change (∫ γ, dist (γ timeZero) (γ timeOne)^2 ∂π) = _ at hcost
  rw [hcost] at hbound
  convert hbound using 1
  dsimp only [timeHalf]
  ring

end WeakHessian
end
end InlinedFile0

end OAI
