import Mathlib
import OAI.Geometry.WeakHessian.Geodesics.GeodesicPlanSupportedBall

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
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MetricSpace X] [BorelSpace X] in
lemma excess_relocation_le (μ ν ρ β : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure β]
    (hρ : ρ ≤ μ-ν) (hmass : β univ = ρ univ) :
    ((μ-ρ+β)-ν) univ ≤ (μ-ν) univ := by
  let δ := μ-ν
  let : IsFiniteMeasure δ := isFiniteMeasure_of_le μ Measure.sub_le
  let : IsFiniteMeasure ρ := isFiniteMeasure_of_le δ hρ
  have hρμ : ρ ≤ μ := hρ.trans Measure.sub_le
  have hu : (μ-ρ+β)-ν ≤ δ-ρ+β := by
    apply Measure.sub_le_of_le_add
    apply Measure.le_of_add_le_add_left (μ := ρ)
    calc
      ρ+(μ-ρ+β) = μ+β := by rw [← add_assoc,add_comm ρ (μ-ρ),Measure.sub_add_cancel_of_le hρμ]
      _ ≤ (δ+ν)+β := add_le_add (measure_le_sub_add μ ν) le_rfl
      _ = (ρ+(δ-ρ)+ν)+β := by rw [add_comm ρ (δ-ρ),Measure.sub_add_cancel_of_le hρ]
      _ = ρ+(δ-ρ+β+ν) := by ac_rfl
  calc
    _ ≤ (δ-ρ+β) univ := hu univ
    _ = δ univ := by
      rw [Measure.add_apply,Measure.sub_apply MeasurableSet.univ hρ,hmass]
      exact tsub_add_cancel_of_le (hρ univ)

lemma cappedExcess_relocation_le (ν : Measure X) [IsFiniteMeasure ν]
    (μ η : ProbabilityMeasure X) (ρ β : Measure X) [IsFiniteMeasure β]
    (hρ : ρ ≤ (μ:Measure X)-ν) (hmass : β univ = ρ univ)
    (hη : (η:Measure X) = (μ:Measure X)-ρ+β) :
    cappedExcess ν η ≤ cappedExcess ν μ := by
  rw [cappedExcess_eq_positivePart,cappedExcess_eq_positivePart,hη]
  exact excess_relocation_le _ _ _ _ hρ hmass

theorem CurvatureDimension.exists_bounded_midpoint_preserving_caps
    [SecondCountableTopology X] [ProperSpace X] {m : Measure X} [SigmaFinite m]
    {K N : ℝ} (hN : 1 < N) (hcd : CurvatureDimension m K N)
    (hfin : FiniteOnBoundedSets m) {μ₀ μ₁ : ProbabilityMeasure X}
    (o : X) (R : ℝ≥0)
    (hb₀ : (μ₀:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (hb₁ : (μ₁:Measure X) (Metric.closedBall o R)ᶜ = 0)
    {C : ℝ≥0∞} (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hd₀ : (μ₀:Measure X) ≤ C • m) (hd₁ : (μ₁:Measure X) ≤ C • m)
    {I : Type*} (W : I → Measure X)
    (hW : ∀ i, W i ≤ (C/((2:ℝ≥0∞)*midpointTauLower K N (2*R))^N) •
      m.restrict (Metric.closedBall o (3*(R:ℝ))))
    (μref : ProbabilityMeasure X) (href : μref ∈ optimalTimeLaws μ₀ μ₁ timeHalf)
    {b : ℝ≥0∞} (hb : 1 < b) (hbt : b ≠ ∞) :
    ∃ μ ∈ optimalTimeLaws μ₀ μ₁ timeHalf,
      (μ:Measure X) ≤ (b*C/((2:ℝ≥0∞)*midpointTauLower K N (2*R))^N) •
        m.restrict (Metric.closedBall o (3*(R:ℝ))) ∧
      ∀ i, cappedExcess (W i) μ ≤ cappedExcess (W i) μref := by
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
      hcd.reroute_midpoint_restriction hN hμ o R hb₀ hb₁ hC hCt hd₀ hd₁ hA hA0 hd hdt hd1
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

theorem CurvatureDimension.exists_sharp_midpoint_preserving_caps
    [SecondCountableTopology X] [ProperSpace X] {m : Measure X} [SigmaFinite m]
    {K N : ℝ} (hN : 1 < N) (hcd : CurvatureDimension m K N)
    (hfin : FiniteOnBoundedSets m) {μ₀ μ₁ : ProbabilityMeasure X}
    (o : X) (R : ℝ≥0)
    (hb₀ : (μ₀:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (hb₁ : (μ₁:Measure X) (Metric.closedBall o R)ᶜ = 0)
    {C : ℝ≥0∞} (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hd₀ : (μ₀:Measure X) ≤ C • m) (hd₁ : (μ₁:Measure X) ≤ C • m)
    {I : Type*} (W : I → Measure X)
    (hW : ∀ i, W i ≤ (C/((2:ℝ≥0∞)*midpointTauLower K N (2*R))^N) •
      m.restrict (Metric.closedBall o (3*(R:ℝ))))
    (μref : ProbabilityMeasure X) (href : μref ∈ optimalTimeLaws μ₀ μ₁ timeHalf) :
    ∃ μ ∈ optimalTimeLaws μ₀ μ₁ timeHalf,
      (μ:Measure X) ≤ (C/((2:ℝ≥0∞)*midpointTauLower K N (2*R))^N) •
        m.restrict (Metric.closedBall o (3*(R:ℝ))) ∧
      ∀ i, cappedExcess (W i) μ ≤ cappedExcess (W i) μref := by
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
    obtain ⟨μ,hμ,hμdom,hcaps⟩ := hcd.exists_bounded_midpoint_preserving_caps
      hN hfin o R hb₀ hb₁ hC hCt hd₀ hd₁ W hW μref href hb hbt
    refine ⟨μ,⟨hμ,hcaps⟩,?_⟩
    simpa only [ν,smul_smul,div_eq_mul_inv,mul_assoc] using hμdom
  exact ⟨μ,hμ.1,hdμ,hμ.2⟩

lemma lower_dominance_of_cap_le (κ : Measure X) [IsFiniteMeasure κ]
    (μ η : ProbabilityMeasure X) (hκμ : κ ≤ (μ:Measure X))
    (hcap : cappedExcess κ η ≤ cappedExcess κ μ) : κ ≤ (η:Measure X) := by
  rw [cappedExcess_eq_positivePart,cappedExcess_eq_positivePart,
    Measure.sub_apply MeasurableSet.univ hκμ] at hcap
  simp only [measure_univ] at hcap
  have ht : κ univ ≤ 1 := by simpa using hκμ univ
  have hb := congrArg (fun ν : Measure X => ν univ)
    (measure_positive_negative_balance (η:Measure X) κ)
  simp only [Measure.add_apply, measure_univ] at hb
  have hh : 1+(κ-(η:Measure X)) univ ≤ 1 := by
    rw [hb]
    exact (add_le_add le_rfl hcap).trans_eq (add_tsub_cancel_of_le ht)
  have hz : (κ-(η:Measure X)) univ = 0 := by
    exact le_antisymm ((ENNReal.add_le_add_iff_left (by simp : (1:ℝ≥0∞) ≠ ∞)).mp (by simpa using hh)) bot_le
  have hz' : κ-(η:Measure X)=0 := Measure.measure_univ_eq_zero.mp hz
  simpa only [hz',zero_add] using measure_le_sub_add κ (η:Measure X)

theorem CurvatureDimension.exists_sharp_midpoint_above_lower
    [SecondCountableTopology X] [ProperSpace X] {m : Measure X} [SigmaFinite m]
    {K N : ℝ} (hN : 1 < N) (hcd : CurvatureDimension m K N)
    (hfin : FiniteOnBoundedSets m) {μ₀ μ₁ : ProbabilityMeasure X}
    (o : X) (R : ℝ≥0)
    (hb₀ : (μ₀:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (hb₁ : (μ₁:Measure X) (Metric.closedBall o R)ᶜ = 0)
    {C : ℝ≥0∞} (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hd₀ : (μ₀:Measure X) ≤ C • m) (hd₁ : (μ₁:Measure X) ≤ C • m)
    (κ : Measure X)
    (hκcap : κ ≤ (C/((2:ℝ≥0∞)*midpointTauLower K N (2*R))^N) •
      m.restrict (Metric.closedBall o (3*(R:ℝ))))
    (μref : ProbabilityMeasure X) (href : μref ∈ optimalTimeLaws μ₀ μ₁ timeHalf)
    (hκref : κ ≤ (μref:Measure X)) :
    ∃ μ ∈ optimalTimeLaws μ₀ μ₁ timeHalf,
      (μ:Measure X) ≤ (C/((2:ℝ≥0∞)*midpointTauLower K N (2*R))^N) •
        m.restrict (Metric.closedBall o (3*(R:ℝ))) ∧ κ ≤ (μ:Measure X) := by
  let : IsFiniteMeasure κ := isFiniteMeasure_of_le (μref:Measure X) hκref
  obtain ⟨μ,hμ,hdμ,hcaps⟩ := hcd.exists_sharp_midpoint_preserving_caps
    hN hfin o R hb₀ hb₁ hC hCt hd₀ hd₁ (fun _ : Unit => κ) (fun _ => hκcap) μref href
  exact ⟨μ,hμ,hdμ,lower_dominance_of_cap_le κ μref μ hκref (hcaps ())⟩

end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end

end OAI
