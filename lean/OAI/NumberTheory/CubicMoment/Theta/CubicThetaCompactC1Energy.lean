import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoreDivision
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCompactInCore
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaC1EnergySums

namespace OAI

/-! Every compact C1 automorphic section belongs to the actual closed
energy graph, by finite reconstruction from smoothed coordinate pieces. -/
noncomputable section
open Set
open scoped BigOperators
namespace CubicFirstMoment

theorem cubicThetaCompactC1_mem_energy (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hc : HasCompactSupport (cubicThetaSectionNorm F)) :
    cubicThetaC1EnergyData F hF hc∈cubicThetaGlobalEnergySpace := by
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
  have hmP (c : CubicThetaQuotient) : cubicThetaC1EnergyData (P c) (hP c) (hcP c)∈
      cubicThetaGlobalEnergySpace := cubicThetaC1CoreFunction_mem_energy c H hH
  have hsum : (∑ c∈A, P c)=F := by
    calc
      _ = ∑ c∈A, cubicThetaSectionCutoff (cubicThetaCoreSquare c) H := by
        apply Finset.sum_congr rfl
        intro c hcA
        exact cubicThetaC1CoreFunction_periodization c H hH
      _ = F := cubicThetaCoreDivision_reconstruction A F hn
  have hm : cubicThetaC1EnergyData (∑ c∈A, P c) (cubicThetaC1Section_sum A P hP)
      (cubicThetaCompactSection_sum A P hcP)∈cubicThetaGlobalEnergySpace := by
    rw [cubicThetaC1EnergyData_sum A P hP hcP]
    exact Submodule.sum_mem _ (fun c hcA => hmP c)
  have he : cubicThetaC1EnergyData (∑ c∈A, P c) (cubicThetaC1Section_sum A P hP)
      (cubicThetaCompactSection_sum A P hcP)=cubicThetaC1EnergyData F hF hc := by
    congr 1
  exact he ▸ hm

end CubicFirstMoment

end

end OAI
