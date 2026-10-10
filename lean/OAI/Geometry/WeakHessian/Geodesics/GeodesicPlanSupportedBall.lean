import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.BoundedEndpointTube
import OAI.Geometry.WeakHessian.LocalBounds.BoundedRnRestriction
import OAI.Geometry.WeakHessian.Calculus.DominatedCompactRerouting

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
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

lemma geodesic_plan_supported_ball (π : Measure (Curve X))
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ) (o : X) (R : ℝ)
    (h₀ : interpolation π timeZero (Metric.closedBall o R)ᶜ = 0)
    (h₁ : interpolation π timeOne (Metric.closedBall o R)ᶜ = 0) (t : Time) :
    interpolation π t (Metric.closedBall o (3*R))ᶜ = 0 := by
  have h0 : ∀ᵐ γ ∂π, dist (γ timeZero) o ≤ R := by
    apply ae_of_ae_map (f := fun γ : Curve X => γ timeZero)
      (p := fun x => dist x o ≤ R) (continuous_eval_const timeZero).measurable.aemeasurable
    exact ae_iff.mpr h₀
  have h1 : ∀ᵐ γ ∂π, dist (γ timeOne) o ≤ R := by
    apply ae_of_ae_map (f := fun γ : Curve X => γ timeOne)
      (p := fun x => dist x o ≤ R) (continuous_eval_const timeOne).measurable.aemeasurable
    exact ae_iff.mpr h₁
  apply ae_iff.mp
  apply (ae_map_iff (continuous_eval_const t).measurable.aemeasurable
    (measurableSet_le (continuous_id.dist continuous_const).measurable measurable_const)).mpr
  filter_upwards [hg,h0,h1] with γ hγ hγ0 hγ1
  exact boundedEndpointTube_range ⟨hγ,hγ0,hγ1⟩ t

lemma scaled_CD_spreading_constant {a q c d : ℝ≥0∞}
    (_hq : q ≠ 0) (_hqt : q ≠ ∞) (hc : c ≠ 0) (hct : c ≠ ∞)
    (hd : d ≠ 0) (hdt : d ≠ ∞) :
    a / ((d*q)⁻¹*(d*c)) = a*q/c := by
  rw [ENNReal.mul_inv (Or.inl hd) (Or.inl hdt)]
  have he : d⁻¹*q⁻¹*(d*c) = q⁻¹*c := by
    calc
      d⁻¹*q⁻¹*(d*c) = (d⁻¹*d)*(q⁻¹*c) := by ac_rfl
      _ = q⁻¹*c := by rw [ENNReal.inv_mul_cancel hd hdt,one_mul]
  rw [he,div_eq_mul_inv,ENNReal.mul_inv (Or.inr hct) (Or.inr hc),inv_inv]
  rw [div_eq_mul_inv,mul_assoc]

lemma CurvatureDimension.reroute_midpoint_restriction
    [SecondCountableTopology X] {m : Measure X} [SigmaFinite m]
    {K N : ℝ} (hN : 1 < N) (hcd : CurvatureDimension m K N)
    {μ₀ μ₁ μ : ProbabilityMeasure X} (hμ : μ ∈ optimalTimeLaws μ₀ μ₁ timeHalf)
    (o : X) (R : ℝ≥0)
    (hb₀ : (μ₀:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (hb₁ : (μ₁:Measure X) (Metric.closedBall o R)ᶜ = 0)
    {C : ℝ≥0∞} (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hd₀ : (μ₀:Measure X) ≤ C • m) (hd₁ : (μ₁:Measure X) ≤ C • m)
    {A : Set X} (hA : MeasurableSet A) (hq : (μ:Measure X) A ≠ 0)
    {d : ℝ≥0∞} (hd : d ≠ 0) (hdt : d ≠ ∞) (hd1 : d ≤ 1) :
    ∃ (β : Measure X) (η : ProbabilityMeasure X), IsFiniteMeasure β ∧
      β univ = d*(μ:Measure X) A ∧ η ∈ optimalTimeLaws μ₀ μ₁ timeHalf ∧
      (η:Measure X) = (μ:Measure X)-d • (μ:Measure X).restrict A+β ∧
      β (Metric.closedBall o (3*(R:ℝ)))ᶜ = 0 ∧
      ∀ B : Set X, MeasurableSet B → β Bᶜ = 0 →
        ((2:ℝ≥0∞)*midpointTauLower K N (2*R))^N*(μ:Measure X) A/C ≤ m B := by
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
    hcd.reroute_finite_subplan hN θ hθ0 o R.property hθb hde0 hde1
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

omit [BorelSpace X] in
lemma CurvatureDimension.optimalTimeLaws_nonempty {m : Measure X} {K N : ℝ}
    (hcd : CurvatureDimension m K N) {μ₀ μ₁ : ProbabilityMeasure X}
    (o : X) (R : ℝ) (hb₀ : (μ₀:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (hb₁ : (μ₁:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (hac₀ : (μ₀:Measure X) ≪ m) (hac₁ : (μ₁:Measure X) ≪ m) (t : Time) :
    (optimalTimeLaws μ₀ μ₁ t).Nonempty := by
  obtain ⟨π,hπ,hgeo,hopt,_⟩ := hcd μ₀ μ₁ inferInstance inferInstance
    (hasSecondMoment_of_ae_dist_le o R (ae_iff.mpr hb₀))
    (hasSecondMoment_of_ae_dist_le o R (ae_iff.mpr hb₁)) hac₀ hac₁
  let := hπ
  let π' : ProbabilityMeasure (Curve X) := ⟨π,inferInstance⟩
  exact ⟨π'.map (fun γ => γ t),π',hgeo,hopt,rfl⟩

lemma CD_cap_support_cancel {a C q b : ℝ≥0∞}
    (ha : a ≠ 0) (hat : a ≠ ∞) (hC : C ≠ 0) (hCt : C ≠ ∞) :
    b*C/a*(a*q/C) = b*q := by
  simp only [div_eq_mul_inv]
  calc
    b*C*a⁻¹*(a*q*C⁻¹) = b*q*(C*C⁻¹)*(a⁻¹*a) := by ac_rfl
    _ = b*q := by rw [ENNReal.mul_inv_cancel hC hCt,ENNReal.inv_mul_cancel ha hat,mul_one,mul_one]

theorem CurvatureDimension.exists_bounded_midpoint
    [SecondCountableTopology X] [ProperSpace X] {m : Measure X} [SigmaFinite m]
    {K N : ℝ} (hN : 1 < N) (hcd : CurvatureDimension m K N)
    (hfin : FiniteOnBoundedSets m) {μ₀ μ₁ : ProbabilityMeasure X}
    (o : X) (R : ℝ≥0)
    (hb₀ : (μ₀:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (hb₁ : (μ₁:Measure X) (Metric.closedBall o R)ᶜ = 0)
    {C : ℝ≥0∞} (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hd₀ : (μ₀:Measure X) ≤ C • m) (hd₁ : (μ₁:Measure X) ≤ C • m)
    {b : ℝ≥0∞} (hb : 1 < b) (hbt : b ≠ ∞) :
    ∃ μ ∈ optimalTimeLaws μ₀ μ₁ timeHalf,
      (μ:Measure X) ≤ (b*C/((2:ℝ≥0∞)*midpointTauLower K N (2*R))^N) •
        m.restrict (Metric.closedBall o (3*(R:ℝ))) := by
  let a : ℝ≥0∞ := ((2:ℝ≥0∞)*midpointTauLower K N (2*R))^N
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
  have hac0 : (μ₀:Measure X) ≪ m := (Measure.absolutelyContinuous_of_le hd₀).trans
    (Measure.AbsolutelyContinuous.rfl.smul_left _)
  have hac1 : (μ₁:Measure X) ≪ m := (Measure.absolutelyContinuous_of_le hd₁).trans
    (Measure.AbsolutelyContinuous.rfl.smul_left _)
  apply exists_dominated_of_compact_rerouting ν
    (hcd.optimalTimeLaws_nonempty o R hb₀ hb₁ hac0 hac1 timeHalf)
    (isCompact_optimalTimeLaws o R hb₀ hb₁ timeHalf)
  intro μ hμ P hP hsur
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
    hcd.reroute_midpoint_restriction hN hμ o R hb₀ hb₁ hC hCt hd₀ hd₁ hA hA0 hd hdt hd1
  let ρ := d • (μ:Measure X).restrict A
  have hρ : ρ ≤ δ := by
    calc
      _ ≤ d • ((n:ℝ≥0∞) • δ) := smul_le_smul_left d hAdom
      _ = δ := by rw [smul_smul,show d*(n:ℝ≥0∞)=1 from ENNReal.inv_mul_cancel hn0 hnt,one_smul]
  refine ⟨ρ,β,η,hβfin,hρ,?_,hη,hηeq,?_⟩
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

lemma isClosed_probability_dominated (ν : Measure X) [IsFiniteMeasure ν] :
    IsClosed {μ : ProbabilityMeasure X | (μ:Measure X) ≤ ν} := by
  have he : {μ : ProbabilityMeasure X | (μ:Measure X) ≤ ν} =
      cappedExcess ν ⁻¹' Iic 0 := by
    ext μ
    change (μ:Measure X) ≤ ν ↔ cappedExcess ν μ ≤ 0
    constructor
    · intro h
      rw [(cappedExcess_eq_zero_iff ν μ).mpr h]
    · intro h
      exact (cappedExcess_eq_zero_iff ν μ).mp (le_antisymm h bot_le)
  rw [he]
  exact (cappedExcess_lowerSemicontinuous ν).isClosed_preimage 0

lemma exists_dominated_of_approximations (ν : Measure X) [IsFiniteMeasure ν]
    {S : Set (ProbabilityMeasure X)} (hc : IsCompact S)
    (h : ∀ b : ℝ≥0∞, 1 < b → b ≠ ∞ → ∃ μ ∈ S, (μ:Measure X) ≤ b • ν) :
    ∃ μ ∈ S, (μ:Measure X) ≤ ν := by
  let b : ℕ → ℝ≥0∞ := fun n => 1+((n+1:ℕ):ℝ≥0∞)⁻¹
  have hb n : 1 < b n := by
    simpa only [b,add_zero] using
      (ENNReal.add_lt_add_left (a := 1) (b := 0) (c := ((n+1:ℕ):ℝ≥0∞)⁻¹)
        (by simp) (ENNReal.inv_pos.mpr (by simp)))
  have hbt n : b n ≠ ∞ := by simp [b]
  have hbf n : IsFiniteMeasure (b n • ν) := by
    constructor
    change b n * ν univ < ∞
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr (hbt n)) (measure_lt_top _ _)
  let T : ℕ → Set (ProbabilityMeasure X) := fun n => S ∩ {μ | (μ:Measure X) ≤ b n • ν}
  have hcl n : IsClosed (T n) := by
    let := hbf n
    exact hc.isClosed.inter (isClosed_probability_dominated _)
  have hne n : (T n).Nonempty := by
    obtain ⟨μ,hμ,hμb⟩ := h (b n) (hb n) (hbt n)
    exact ⟨μ,hμ,hμb⟩
  have hmono n : T (n+1) ⊆ T n := by
    intro μ hμ
    change μ ∈ S ∧ (μ:Measure X) ≤ b (n+1) • ν at hμ
    change μ ∈ S ∧ (μ:Measure X) ≤ b n • ν
    refine ⟨hμ.1,hμ.2.trans ?_⟩
    intro A
    change b (n+1)*ν A ≤ b n*ν A
    apply mul_le_mul' _ le_rfl
    apply add_le_add le_rfl
    apply ENNReal.inv_le_inv.mpr
    exact_mod_cast Nat.le_succ (n+1)
  have hc0 : IsCompact (T 0) := hc.of_isClosed_subset (hcl 0) inter_subset_left
  obtain ⟨μ,hμ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed T hmono hne hc0 hcl
  refine ⟨μ,(mem_iInter.mp hμ 0).1,?_⟩
  have hblim : Tendsto b atTop (𝓝 1) := by
    simpa only [b,Function.comp_def,add_zero] using
      (tendsto_const_nhds.add (ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)))
  intro A
  have H : ∀ n, (μ:Measure X) A ≤ b n*ν A := fun n => (mem_iInter.mp hμ n).2 A
  have Hlim := (ENNReal.continuous_mul_const (measure_ne_top ν A)).tendsto 1 |>.comp hblim
  simpa only [one_mul] using ge_of_tendsto Hlim (Eventually.of_forall H)

theorem CurvatureDimension.exists_sharply_bounded_midpoint
    [SecondCountableTopology X] [ProperSpace X] {m : Measure X} [SigmaFinite m]
    {K N : ℝ} (hN : 1 < N) (hcd : CurvatureDimension m K N)
    (hfin : FiniteOnBoundedSets m) {μ₀ μ₁ : ProbabilityMeasure X}
    (o : X) (R : ℝ≥0)
    (hb₀ : (μ₀:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (hb₁ : (μ₁:Measure X) (Metric.closedBall o R)ᶜ = 0)
    {C : ℝ≥0∞} (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hd₀ : (μ₀:Measure X) ≤ C • m) (hd₁ : (μ₁:Measure X) ≤ C • m) :
    ∃ μ ∈ optimalTimeLaws μ₀ μ₁ timeHalf,
      (μ:Measure X) ≤ (C/((2:ℝ≥0∞)*midpointTauLower K N (2*R))^N) •
        m.restrict (Metric.closedBall o (3*(R:ℝ))) := by
  let a : ℝ≥0∞ := ((2:ℝ≥0∞)*midpointTauLower K N (2*R))^N
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
  apply exists_dominated_of_approximations ν (isCompact_optimalTimeLaws o R hb₀ hb₁ timeHalf)
  intro b hb hbt
  obtain ⟨μ,hμ,hμdom⟩ := hcd.exists_bounded_midpoint hN hfin o R hb₀ hb₁ hC hCt hd₀ hd₁ hb hbt
  refine ⟨μ,hμ,?_⟩
  simpa only [ν,smul_smul,div_eq_mul_inv,mul_assoc] using hμdom

end WeakHessian

end
end InlinedFile0

end OAI
