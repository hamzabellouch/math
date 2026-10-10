import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.OnlineInitial
import OAI.Combinatorics.MatchingCount.Complexity.OnlineScheduleCost

namespace OAI

namespace MatchingFPRAS.OnlineInitial
open TreeTyped TreeFraction OnlineSchedule Polynomial NumericBounds

lemma work_root : WorkBound rootRealizer id := by
  unfold rootRealizer
  apply work_then_polynomial _ polynomial_findRoot
  apply work_pair _ _ (4*X+1) (fun n=>by simpa using weight_nat_numeric n)
  · exact work_of_polynomial (polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant _))
      polynomial_subtract) (4*X+1) (fun n=>by simpa using weight_nat_numeric n)
  · exact work_composition (work_of_polynomial polynomial_identity (4*X+1)
      (fun n=>by simpa using weight_nat_numeric n)) fuel_numeric_work X (by simp)
lemma work_initialScale : WorkBound initialScaleRealizer id := by
  unfold initialScaleRealizer
  apply work_then_polynomial _ polynomial_div
  apply work_pair _ _ (4*X+1) (fun n=>by simpa using weight_nat_numeric n)
  · exact work_of_polynomial (polynomial_constant _) (4*X+1) (fun n=>by simpa using weight_nat_numeric n)
  · exact work_pair work_root (work_of_polynomial (polynomial_constant _) (4*X+1)
      (fun n=>by simpa using weight_nat_numeric n)) (4*X+1) (fun n=>by simpa using weight_nat_numeric n)
lemma polynomial_scaleVector : PolynomialTime scaleVectorRealizer := by
  unfold scaleVectorRealizer
  apply polynomial_congr
  apply work_then_polynomial _ (polynomial_mapWith (polynomial_pair polynomial_second polynomial_first))
  apply work_pair _ polynomial_identity X (by simp)
  exact work_composition polynomial_listLength work_initialScale X (fun vs=>by simpa using list_length_le_weight vs)
lemma polynomial_count : PolynomialTime countRealizer := by
  unfold countRealizer nRealizer Realizer.fst Realizer.snd
  apply polynomial_composition _ polynomial_sampleCount
  tree_cost
lemma polynomial_seedD : PolynomialTime seedDRealizer := by
  unfold seedDRealizer Realizer.fst
  apply polynomial_pair polynomial_first
  apply polynomial_pair polynomial_second
  apply polynomial_composition _ polynomial_distortion
  tree_cost

def configNumeric (x : Config) : ℕ := x.1.1.1.1.length+x.1.2+x.2.1+x.2.2+
  ladderSchedule (x.2,x.1.2)+Transport.ladderQ x.2.1 x.2.2
def configSize (x : Config) : ℕ := configNumeric x+weight x
def seedSize (x : Seed) : ℕ := x.1.1.length+natCeil (inverse x.2.1)+configNumeric (config x)+weight x
lemma weight_configSize (x : Config) : weight x ≤ configSize x := by unfold configSize;omega
lemma weight_seedSize (x : Seed) : weight x ≤ seedSize x := by unfold seedSize;omega
lemma config_fields (x : Config) : x.1.1.1.1.length ≤ configSize x ∧ x.1.2 ≤ configSize x ∧
    x.2.1 ≤ configSize x ∧ x.2.2 ≤ configSize x ∧
    ladderSchedule (x.2,x.1.2) ≤ configSize x ∧Transport.ladderQ x.2.1 x.2.2 ≤ configSize x := by
  unfold configSize configNumeric;omega
lemma seed_fields (x : Seed) : x.1.1.length ≤ seedSize x ∧ natCeil (inverse x.2.1) ≤ seedSize x ∧
    coolingSchedule (x.1.1.length,x.2.1) ≤ seedSize x ∧configNumeric (config x) ≤ seedSize x := by
  unfold seedSize configNumeric config seedD seedN seedK
  dsimp only
  omega

lemma work_seedK : WorkBound seedKRealizer seedSize := by
  have lift {A : Type} [Codec A] {f : Seed→A} {F : Realizer f} (hF : PolynomialTime F) :
      WorkBound F seedSize := work_of_polynomial hF X (fun x=>by simpa using weight_seedSize x)
  unfold seedKRealizer
  apply work_congr
  apply work_pair (lift polynomial_identity) _ X (fun x=>by simpa using weight_seedSize x)
  apply work_comp_bound (lift (polynomial_pair (polynomial_composition (polynomial_fst polynomial_first)
    polynomial_listLength) (polynomial_fst polynomial_second))) work_coolingSchedule
  have hw:=NumericBounds.weight (lift (polynomial_pair (polynomial_composition (polynomial_fst polynomial_first)
    polynomial_listLength) (polynomial_fst polynomial_second)))
  exact add (add (of_le (fun x=>(seed_fields x).1)) (of_le (fun x=>(seed_fields x).2.1))) hw

def seedNSize (x : Seed×ℕ) : ℕ := x.1.1.1.length+x.2+weight x
lemma work_seedN : WorkBound seedNRealizer seedNSize := by
  have lift {A : Type} [Codec A] {f : (Seed×ℕ)→A} {F : Realizer f} (hF : PolynomialTime F) :
      WorkBound F seedNSize := work_of_polynomial hF X (fun x=>by simp [seedNSize])
  unfold seedNRealizer
  apply work_congr
  apply work_pair (lift polynomial_identity) _ X (fun x=>by simp [seedNSize])
  apply work_comp_bound (lift (polynomial_pair (polynomial_composition (polynomial_fst (polynomial_fst polynomial_first))
    polynomial_listLength) polynomial_second)) work_vertexNumber
  have hw:=NumericBounds.weight (lift (polynomial_pair (polynomial_composition (polynomial_fst (polynomial_fst polynomial_first))
    polynomial_listLength) polynomial_second))
  exact add (add (of_le (fun x=>by dsimp only [Function.comp_apply]; unfold seedNSize;omega)) (of_le (fun x=>by dsimp only [Function.comp_apply]; unfold seedNSize;omega))) hw
lemma work_config : WorkBound configRealizer seedSize := by
  unfold configRealizer
  apply work_then_polynomial _ polynomial_seedD
  apply work_comp_bound work_seedK work_seedN
  have hw:=NumericBounds.weight work_seedK
  exact add (add (of_le (fun x=>(seed_fields x).1)) (of_le (fun x=>(seed_fields x).2.2.1))) hw
lemma bound_configSize : Bound (configSize ∘ config) seedSize :=
  add (of_le (fun x=>(seed_fields x).2.2.2)) (NumericBounds.weight work_config)
end MatchingFPRAS.OnlineInitial

end OAI
