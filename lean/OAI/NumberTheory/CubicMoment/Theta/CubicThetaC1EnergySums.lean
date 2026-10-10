import OAI.NumberTheory.CubicMoment.Theta.CubicThetaC1EnergyLinear

namespace OAI

/-! Finite sums of compact C1 sections preserve their actual
value-gradient data. This permits finite reconstruction from chart pieces. -/
noncomputable section
open Set
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaCompactSection_add (F G : CubicThetaSection)
    (hF : HasCompactSupport (cubicThetaSectionNorm F))
    (hG : HasCompactSupport (cubicThetaSectionNorm G)) :
    HasCompactSupport (cubicThetaSectionNorm (F+G)) := by
  apply (hF.union hG).of_isClosed_subset isClosed_closure
  apply closure_minimal _ (hF.union hG).isClosed
  intro q hq
  by_contra h
  have hFq : cubicThetaSectionNorm F q=0 :=
    image_eq_zero_of_notMem_tsupport (fun hFq => h (Or.inl hFq))
  have hGq : cubicThetaSectionNorm G q=0 :=
    image_eq_zero_of_notMem_tsupport (fun hGq => h (Or.inr hGq))
  apply hq
  change ‖F.val (cubicThetaQuotientLift q)+G.val (cubicThetaQuotientLift q)‖=0
  rw [norm_eq_zero.mp hFq,norm_eq_zero.mp hGq,add_zero,norm_zero]

lemma cubicThetaC1EnergyData_add (F G : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (hG : ContDiffOn ℝ 1 (cubicThetaSectionFunction G) {y : ℂ × ℝ | 0<y.2})
    (hcF : HasCompactSupport (cubicThetaSectionNorm F))
    (hcG : HasCompactSupport (cubicThetaSectionNorm G)) :
    cubicThetaC1EnergyData (F+G) (hF.add hG) (cubicThetaCompactSection_add F G hcF hcG)=
      cubicThetaC1EnergyData F hF hcF+cubicThetaC1EnergyData G hG hcG := by
  have h := cubicThetaC1EnergyData_sub (F+G) G (hF.add hG) hG
    (cubicThetaCompactSection_add F G hcF hcG) hcG
  have he : cubicThetaC1EnergyData F hF hcF=
      cubicThetaC1EnergyData (F+G) (hF.add hG) (cubicThetaCompactSection_add F G hcF hcG)-
        cubicThetaC1EnergyData G hG hcG := by
    have heq : F+G-G=F := add_sub_cancel_right F G
    exact (cubicThetaC1EnergyData_congr heq _ _ _ _).symm.trans h
  exact (eq_sub_iff_add_eq.mp he).symm

lemma cubicThetaSectionFunction_sum {ι : Type*} (A : Finset ι) (F : ι → CubicThetaSection) :
    cubicThetaSectionFunction (∑ i∈A, F i)=fun y => ∑ i∈A, cubicThetaSectionFunction (F i) y := by
  funext y
  simp [cubicThetaSectionFunction]

lemma cubicThetaC1Section_sum {ι : Type*} (A : Finset ι) (F : ι → CubicThetaSection)
    (hF : ∀ i, ContDiffOn ℝ 1 (cubicThetaSectionFunction (F i)) {y : ℂ × ℝ | 0<y.2}) :
    ContDiffOn ℝ 1 (cubicThetaSectionFunction (∑ i∈A, F i)) {y : ℂ × ℝ | 0<y.2} := by
  rw [cubicThetaSectionFunction_sum]
  exact ContDiffOn.sum (fun i _ => hF i)

lemma cubicThetaCompactSection_sum {ι : Type*} (A : Finset ι) (F : ι → CubicThetaSection)
    (hc : ∀ i, HasCompactSupport (cubicThetaSectionNorm (F i))) :
    HasCompactSupport (cubicThetaSectionNorm (∑ i∈A, F i)) := by
  classical
  induction A using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      change HasCompactSupport (fun _ : CubicThetaQuotient => ‖(0:ℂ)‖)
      have hz : (fun _ : CubicThetaQuotient => ‖(0:ℂ)‖)=(0 : CubicThetaQuotient → ℝ) := by
        funext q
        exact norm_zero
      rw [hz]
      exact HasCompactSupport.zero
  | @insert i A hi ih =>
      simpa only [Finset.sum_insert hi] using cubicThetaCompactSection_add (F i) (∑ j∈A, F j) (hc i) ih

lemma cubicThetaC1EnergyData_sum {ι : Type*} (A : Finset ι) (F : ι → CubicThetaSection)
    (hF : ∀ i, ContDiffOn ℝ 1 (cubicThetaSectionFunction (F i)) {y : ℂ × ℝ | 0<y.2})
    (hc : ∀ i, HasCompactSupport (cubicThetaSectionNorm (F i))) :
    cubicThetaC1EnergyData (∑ i∈A, F i) (cubicThetaC1Section_sum A F hF)
      (cubicThetaCompactSection_sum A F hc)=∑ i∈A, cubicThetaC1EnergyData (F i) (hF i) (hc i) := by
  classical
  induction A using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact (cubicThetaC1EnergyData_smooth (0 : cubicThetaSmoothTests)).trans (map_zero _)
  | @insert i A hi ih =>
      simp only [Finset.sum_insert hi]
      rw [cubicThetaC1EnergyData_add (F i) (∑ j∈A, F j) (hF i)
        (cubicThetaC1Section_sum A F hF) (hc i) (cubicThetaCompactSection_sum A F hc)]
      rw [ih]

end CubicFirstMoment

end

end OAI
