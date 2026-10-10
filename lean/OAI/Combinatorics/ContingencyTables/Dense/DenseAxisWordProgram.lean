import OAI.Combinatorics.ContingencyTables.Dense.DenseAxisSemantics
import OAI.Combinatorics.ContingencyTables.Dense.DenseAxisBits

namespace OAI

/-! # Binary-word decoding for a dense coordinate proposal -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary

abbrev AxisWordData := (ℕ×List ℕ)×List Bool

def axisWordStep (z : AxisWordData) : Option (List ℕ) :=
  axisListStep ((z.1,StackAddition.value z.2/2),decide (StackAddition.value z.2%2=1))

def axisWordStepRealizer : Realizer axisWordStep := by
  let V : Realizer (fun z : AxisWordData => StackAddition.value z.2) := composition second bitValue
  let I := composition (pair V (constant 2)) quotient
  let S := composition (pair (composition (pair V (constant 2)) remainder) (constant 1)) natEqual
  exact composition (pair (pair first I) S) axisListStepRealizer

theorem polynomial_axisWordStep : PolynomialTime axisWordStepRealizer := by
  have hv : PolynomialTime (composition
      (second (A := ℕ×List ℕ) (B := List Bool)) bitValue) :=
    polynomial_composition polynomial_second polynomial_bitValue
  have hi := polynomial_composition (polynomial_pair hv (polynomial_constant 2)) polynomial_quotient
  have hs := polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair hv (polynomial_constant 2)) polynomial_remainder)
    (polynomial_constant 1)) polynomial_natEqual
  unfold axisWordStepRealizer
  exact polynomial_composition (polynomial_pair (polynomial_pair polynomial_first hi) hs)
    polynomial_axisListStep

lemma directionCode_first {q : ℕ} (v : Fin (q*2)) :
    ((directionCodeEquiv q).symm v).1.val=v.val/2 := rfl

lemma directionCode_second {q : ℕ} (v : Fin (q*2)) :
    ((directionCodeEquiv q).symm v).2=decide (v.val%2=1) := by
  have hf (b : Fin 2) : finTwoEquiv b=decide (b.val=1) := by
    fin_cases b <;> rfl
  exact hf _

/-- A binary index gives exactly the signed coordinate code used by
the finite dense-chain transition; unused indices still reject. -/
theorem axisWordStep_eq {q K k : ℕ} (a : Grid (I := Fin q) K) (bits : Fin k → Bool) :
    axisWordStep ((K,gridNatCode a),List.ofFn bits)=
      (axisCodeStep a (FairBits.binaryWordEquiv k bits)).map gridNatCode := by
  rw [axisWordStep,bitValue_eq_word]
  let v := FairBits.binaryWordEquiv k bits
  change axisListStep (((K,gridNatCode a),v.val/2),decide (v.val%2=1))=
    (axisCodeStep a v).map gridNatCode
  by_cases hv : v.val<q*2
  · let u : Fin (q*2) := ⟨v.val,hv⟩
    let dir := (directionCodeEquiv q).symm u
    have hfirst : dir.1.val=v.val/2 := directionCode_first u
    have hsecond : dir.2=decide (v.val%2=1) := directionCode_second u
    rw [←hfirst,←hsecond,axisListStep_eq]
    simp only [axisCodeStep,dite_eq_left hv]
    rfl
  · have hi : ¬v.val/2<q := by omega
    have hlen : (gridNatCode a).length=q := by simp only [gridNatCode,List.length_ofFn]
    simp only [axisListStep,hlen,ite_eq_right hi,axisCodeStep,dite_eq_right hv,Option.map_none]

end ContingencyTables.DensePrograms

end OAI
