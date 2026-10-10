import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticWeakDefect
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCompactC1Energy

namespace OAI

/-! Finite arithmetic chart reconstruction and continuity extend the
literal remainder's weak equation to every global energy test. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaArithmeticWeakDefect_compact {s : ℂ} (hs : 3<s.re)
    (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hc : HasCompactSupport (cubicThetaSectionNorm F)) :
    cubicThetaArithmeticWeakDefect s hs (cubicThetaC1EnergyData F hF hc)=0 := by
  obtain ⟨S,V,hSV⟩ := cubicThetaCompact_subset_core hc
  obtain ⟨A,hA⟩ := cubicThetaCoreDenominator_covers S V
  have hn : ∀ q∈tsupport (cubicThetaSectionNorm F), cubicThetaCoreDenominator A q≠0 := by
    intro q hq
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one (hA q (hSV hq)))
  let D := cubicThetaCoreDenominator A
  let H := cubicThetaSectionDivide F D (cubicThetaCoreDenominator_continuous A) hn
  have hH : ContDiffOn ℝ 1 (cubicThetaSectionFunction H) {y : ℂ × ℝ | 0<y.2} :=
    cubicThetaSectionDivide_regular F hF D (cubicThetaCoreDenominator_continuous A) hn
      (cubicThetaCoreDenominator_pullback A)
  let P := fun c : CubicThetaQuotient => cubicThetaPoincareSection
    (cubicThetaCoordinateSeed (cubicThetaC1CoreFunction c H)
      (cubicThetaC1CoreFunction_regular c H hH).continuous
      (cubicThetaC1CoreFunction_compact c H)
      ((cubicThetaC1CoreFunction_support c H).trans (cubicThetaCoreProfile_support_positive c)))
  have hP (c : CubicThetaQuotient) :
      ContDiffOn ℝ 1 (cubicThetaSectionFunction (P c)) {y : ℂ × ℝ | 0<y.2} :=
    cubicThetaCoordinateSection_regular (cubicThetaC1CoreFunction_regular c H hH)
      (cubicThetaC1CoreFunction_compact c H)
      ((cubicThetaC1CoreFunction_support c H).trans (cubicThetaCoreProfile_support_positive c))
  have hcP (c : CubicThetaQuotient) : HasCompactSupport (cubicThetaSectionNorm (P c)) :=
    cubicThetaPoincareSection_compact _
  have hzP (c : CubicThetaQuotient) :
      cubicThetaArithmeticWeakDefect s hs (cubicThetaC1EnergyData (P c) (hP c) (hcP c))=0 := by
    apply cubicThetaArithmeticWeakDefect_coordinate hs
      (cubicThetaC1CoreFunction_regular c H hH) (cubicThetaC1CoreFunction_compact c H)
      (cubicThetaCoreProfile_compact c) (cubicThetaCoreProfile_support_positive c)
      (cubicThetaC1CoreFunction_support c H)
      (cubicThetaCoveringChart (cubicThetaQuotientLift c)) (cubicThetaCoveringChart_coe _)
    rintro p ⟨y,hy,rfl⟩
    exact (cubicThetaCoreProfile_support_target c hy).2
  have hsum : (∑ c∈A, P c)=F := by
    calc
      _ = ∑ c∈A, cubicThetaSectionCutoff (cubicThetaCoreSquare c) H := by
        apply Finset.sum_congr rfl
        intro c hcA
        exact cubicThetaC1CoreFunction_periodization c H hH
      _ = F := cubicThetaCoreDivision_reconstruction A F hn
  have he : cubicThetaC1EnergyData F hF hc=
      ∑ c∈A, cubicThetaC1EnergyData (P c) (hP c) (hcP c) := by
    rw [← cubicThetaC1EnergyData_sum A P hP hcP]
    congr 1
    exact hsum.symm
  rw [he,map_sum]
  exact Finset.sum_eq_zero (fun c _ => hzP c)

lemma cubicThetaArithmeticWeakDefect_energy {s : ℂ} (hs : 3<s.re)
    (v : cubicThetaGlobalEnergySpace) :
    cubicThetaArithmeticWeakDefect s hs (v:CubicThetaGlobalEnergyAmbient)=0 := by
  have hc : IsClosed {u : CubicThetaGlobalEnergyAmbient | cubicThetaArithmeticWeakDefect s hs u=0} :=
    isClosed_eq (cubicThetaArithmeticWeakDefect_continuous s hs) continuous_const
  have hr : (cubicThetaGlobalEnergyGraph.range : Set CubicThetaGlobalEnergyAmbient)⊆
      {u | cubicThetaArithmeticWeakDefect s hs u=0} := by
    rintro u ⟨F,rfl⟩
    rw [← cubicThetaC1EnergyData_smooth F]
    exact cubicThetaArithmeticWeakDefect_compact hs F (F.property.1.of_le (by simp)) F.property.2
  have hv : (v:CubicThetaGlobalEnergyAmbient)∈
      closure (cubicThetaGlobalEnergyGraph.range : Set CubicThetaGlobalEnergyAmbient) := v.property
  exact closure_minimal hr hc hv

theorem cubicThetaArithmetic_global_weak {s : ℂ} (hs : 3<s.re)
    (v : cubicThetaGlobalEnergySpace) :
    inner ℂ (cubicThetaGlobalEnergyGradient v)
      (cubicThetaGlobalEnergyGradient (cubicThetaArithmeticEnergy s hs))+
    s*(s-2)*inner ℂ (cubicThetaGlobalInclusion v)
      (cubicThetaGlobalInclusion (cubicThetaArithmeticEnergy s hs))=
    inner ℂ (cubicThetaGlobalInclusion v) (cubicThetaForcingL2 s) := by
  exact sub_eq_zero.mp (cubicThetaArithmeticWeakDefect_energy hs v)

end CubicFirstMoment

end

end OAI
