import OAI.Combinatorics.ContingencyTables.Counting.CompanionComputedProposal
import OAI.Combinatorics.ContingencyTables.Counting.CompanionTraceProgram
import OAI.Combinatorics.ContingencyTables.Counting.CompanionRationalUpdates

namespace OAI

/-! # Executable counts in an outer counting phase

The stored trajectory is scanned directly. Both the transversal count
and each labelled defect count use the actual polynomial occupancy
tests. No set-state enumeration is performed.
-/

namespace ContingencyTables.CompanionPhaseCounts

open MatchingFPRAS.TreeTyped ProfilePrograms CompanionChainValidator
open CompanionTraceProgram CompanionOrderedProposal CompanionArithmeticProposal
open CompanionFactorialApplication CompanionBooleanPhase
open CommonBasesFPRAS TwoLiftStates
open scoped Classical

def plainCountCode (z : ReturnInput) : ℕ :=
  (z.2.filter (fun xs => pairedPlainTest (z.1,xs))).length

def plainCountRealizer : Realizer plainCountCode :=
  composition (filterWith pairedPlainTestRealizer) listLength

theorem polynomial_plainCount : PolynomialTime plainCountRealizer :=
  polynomial_composition (polynomial_filterWith polynomial_pairedPlainTest) polynomial_listLength

def pairedDefectTest (z : ValidatorInput×(ℕ×ℕ)) : Bool :=
  defectTest (((z.1.1.map (fun ij => z.1.2.getD ij.1 0),
    z.1.1.map (fun ij => z.1.2.getD ij.2 0)),1),z.2)

def pairedDefectTestRealizer : Realizer pairedDefectTest :=
  composition (pair (pair (pair
    (composition (pair (composition first second) (composition first first))
      (mapWith pairFirstLookup))
    (composition (pair (composition first second) (composition first first))
      (mapWith pairSecondLookup))) (constant 1)) second) defectTestRealizer

theorem polynomial_pairedDefectTest : PolynomialTime pairedDefectTestRealizer :=
  polynomial_composition (polynomial_pair (polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second)
      (polynomial_composition polynomial_first polynomial_first))
      (polynomial_mapWith polynomial_pairFirstLookup))
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second)
      (polynomial_composition polynomial_first polynomial_first))
      (polynomial_mapWith polynomial_pairSecondLookup))) (polynomial_constant 1))
    polynomial_second) polynomial_defectTest

abbrev DefectCountInput := ReturnInput×(ℕ×ℕ)

def defectItem (z : (List (ℕ×ℕ)×(ℕ×ℕ))×List ℕ) : Bool :=
  pairedDefectTest ((z.1.1,z.2),z.1.2)

def defectItemRealizer : Realizer defectItem :=
  composition (pair (pair (composition first first) second) (composition first second))
    pairedDefectTestRealizer

lemma polynomial_defectItem : PolynomialTime defectItemRealizer :=
  polynomial_composition (polynomial_pair (polynomial_pair
    (polynomial_composition polynomial_first polynomial_first) polynomial_second)
    (polynomial_composition polynomial_first polynomial_second)) polynomial_pairedDefectTest

def defectCountCode (z : DefectCountInput) : ℕ :=
  (z.1.2.filter (fun xs => pairedDefectTest ((z.1.1,xs),z.2))).length

def defectCountRealizer : Realizer defectCountCode :=
  composition (composition (pair (pair (composition first first) second)
    (composition first second)) (filterWith defectItemRealizer)) listLength

theorem polynomial_defectCount : PolynomialTime defectCountRealizer :=
  polynomial_composition (polynomial_composition (polynomial_pair (polynomial_pair
    (polynomial_composition polynomial_first polynomial_first) polynomial_second)
    (polynomial_composition polynomial_first polynomial_second))
    (polynomial_filterWith polynomial_defectItem)) polynomial_listLength

noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]
variable (A : Instance I J) {p m : ℕ} (g : Fin p ≃ Labels A)
  (e : (Labels A×Bool) ≃ Fin m)

lemma plainTest_ordered (S : Set (Labels A×Bool)) :
    pairedPlainTest (orderedCatalog A g e,encodeSet e S)=true ↔ PlainState pairs S := by
  unfold pairedPlainTest orderedCatalog
  simp only [List.map_ofFn]
  change balancedTest ((List.ofFn (fun i : Fin p => (encodeSet e S).getD (e (g i,false)).val 0),
    List.ofFn (fun i : Fin p => (encodeSet e S).getD (e (g i,true)).val 0)),1)=true ↔ _
  simp only [encodeSet,getD_setProfile,setProfile,coordinateSet,Set.mem_preimage,
    Equiv.symm_apply_apply]
  rw [balancedTest_ofFn,plain_iff_occupancy]
  change (∀ i,occupancy S (g i)=1) ↔ ∀ a,occupancy S a=1
  constructor
  · intro h a
    simpa only [Equiv.apply_symm_apply] using h (g.symm a)
  · intro h i
    exact h (g i)

lemma defectTest_ordered (S : Set (Labels A×Bool)) (i j : Fin p) :
    pairedDefectTest ((orderedCatalog A g e,encodeSet e S),(i.val,j.val))=true ↔
      DefectState pairs (pair (g i)) (pair (g j)) S := by
  classical
  unfold pairedDefectTest orderedCatalog
  simp only [List.map_ofFn]
  change defectTest (((List.ofFn (fun k : Fin p => (encodeSet e S).getD (e (g k,false)).val 0),
    List.ofFn (fun k : Fin p => (encodeSet e S).getD (e (g k,true)).val 0)),1),
    (i.val,j.val))=true ↔ _
  simp only [encodeSet,getD_setProfile,setProfile,coordinateSet,Set.mem_preimage,
    Equiv.symm_apply_apply]
  rw [defectTest_ofFn,defect_iff_occupancy]
  constructor
  · rintro ⟨hij,h⟩
    refine ⟨fun he => hij (g.injective he),fun a => ?_⟩
    have hh := h (g.symm a)
    by_cases hai : a=g i <;> by_cases haj : a=g j
    all_goals simpa only [occupancy,Equiv.apply_symm_apply,Equiv.symm_apply_eq,
      hai,haj,ite_true,ite_false] using hh
  · rintro ⟨hij,h⟩
    refine ⟨fun he => hij (congrArg g he),fun k => ?_⟩
    simpa only [occupancy,Equiv.apply_eq_iff_eq] using h (g k)

theorem plainCount_code (states : List (Set (Labels A×Bool))) :
    plainCountCode (orderedCatalog A g e,states.map (encodeSet e))=
      CompanionRationalUpdates.plainCount A states := by
  unfold plainCountCode CompanionRationalUpdates.plainCount
  rw [List.filter_map,List.length_map,List.countP_eq_length_filter]
  congr 1
  apply List.filter_congr
  intro S _
  exact Bool.eq_iff_iff.mpr (by simp only [Function.comp_apply,plainTest_ordered,decide_eq_true_eq])

theorem defectCount_code (states : List (Set (Labels A×Bool))) (i j : Fin p) :
    defectCountCode ((orderedCatalog A g e,states.map (encodeSet e)),(i.val,j.val))=
      CompanionRationalUpdates.defectCount A states (pair (g i)) (pair (g j)) := by
  unfold defectCountCode CompanionRationalUpdates.defectCount
  rw [List.filter_map,List.length_map,List.countP_eq_length_filter]
  congr 1
  apply List.filter_congr
  intro S _
  exact Bool.eq_iff_iff.mpr (by simp only [Function.comp_apply,defectTest_ordered,decide_eq_true_eq])

end
end ContingencyTables.CompanionPhaseCounts

end OAI
