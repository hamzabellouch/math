import OAI.Combinatorics.ContingencyTables.Counting.CompanionMultiplierProgram

namespace OAI

/-! # The full multiplier update and abort test as list programs

Only the polynomial list of labelled pairs is traversed. Every matrix
entry is updated from the actual plain and defect counts of the stored
trajectory. The count check includes every off-diagonal labelled type.
-/

namespace ContingencyTables.CompanionMultiplierMatrixProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial
open CompanionPhaseCounts CompanionMultiplierProgram CompanionOrderedProposal CompanionTraceProgram
open CompanionFactorialApplication CompanionArithmeticProposal CompanionRationalUpdates
open CommonBasesFPRAS
open scoped Classical

abbrev FractionMatrix := List (List TreeFraction.Fraction)
abbrev Input := ReturnInput×FractionMatrix

def indices (z : ReturnInput) : List ℕ := List.range z.1.length

def indicesRealizer : Realizer indices := composition (composition first listLength) range

lemma polynomial_indices : PolynomialTime indicesRealizer := by
  apply polynomial_boundedRange (polynomial_composition polynomial_first polynomial_listLength) X
  intro z
  simpa only [Function.comp_apply,eval_X] using
    (list_length_le_weight z.1).trans (weight_fst z)

def readEntry (z : FractionMatrix×(ℕ×ℕ)) : TreeFraction.Fraction :=
  (z.1.getD z.2.1 []).getD z.2.2 (0,1)

def readEntryRealizer : Realizer readEntry :=
  composition (pair (composition (pair first (composition second first)) (getDFast []))
    (composition second second)) (getDFast (0,1))

lemma polynomial_readEntry : PolynomialTime readEntryRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_first
      (polynomial_composition polynomial_second polynomial_first)) (polynomial_getDFast []))
    (polynomial_composition polynomial_second polynomial_second)) (polynomial_getDFast (0,1))

def updateEntry (z : Input×(ℕ×ℕ)) : TreeFraction.Fraction :=
  updateCode ((z.1.1,z.2),readEntry (z.1.2,z.2))

def updateEntryRealizer : Realizer updateEntry :=
  composition (pair (pair (composition first first) second)
    (composition (pair (composition first second) second) readEntryRealizer)) updateCodeRealizer

lemma polynomial_updateEntry : PolynomialTime updateEntryRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_pair (polynomial_composition polynomial_first polynomial_first) polynomial_second)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second) polynomial_second)
      polynomial_readEntry)) polynomial_updateCode

def rowEntry (z : (Input×ℕ)×ℕ) : TreeFraction.Fraction :=
  updateEntry (z.1.1,(z.1.2,z.2))

def rowEntryRealizer : Realizer rowEntry :=
  composition (pair (composition first first) (pair (composition first second) second))
    updateEntryRealizer

lemma polynomial_rowEntry : PolynomialTime rowEntryRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_first)
    (polynomial_pair (polynomial_composition polynomial_first polynomial_second) polynomial_second))
    polynomial_updateEntry

def updateRow (z : Input×ℕ) : List TreeFraction.Fraction :=
  (indices z.1.1).map (fun j => rowEntry (z,j))

def updateRowRealizer : Realizer updateRow :=
  composition (pair identity (composition (composition first first) indicesRealizer))
    (mapWith rowEntryRealizer)

lemma polynomial_updateRow : PolynomialTime updateRowRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_indices)) (polynomial_mapWith polynomial_rowEntry)

def updateMatrix (z : Input) : FractionMatrix :=
  (indices z.1).map (fun i => updateRow (z,i))

def updateMatrixRealizer : Realizer updateMatrix :=
  composition (pair identity (composition first indicesRealizer)) (mapWith updateRowRealizer)

theorem polynomial_updateMatrix : PolynomialTime updateMatrixRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition polynomial_first polynomial_indices))
    (polynomial_mapWith polynomial_updateRow)

/-- Diagonal matrix entries do not name defect classes. -/
def positiveEntry (z : DefectCountInput) : Bool :=
  decide (z.2.1=z.2.2 ∨ 0<defectCountCode z)

def positiveEntryRealizer : Realizer positiveEntry :=
  (choose (composition second natEqual) (constant true)
    (composition (pair (constant 0) defectCountRealizer) less)).congr (by
      intro z
      by_cases h : z.2.1=z.2.2 <;> simp [positiveEntry,h])

lemma polynomial_positiveEntry : PolynomialTime positiveEntryRealizer := by
  unfold positiveEntryRealizer
  apply polynomial_congr
  exact polynomial_choose (polynomial_composition polynomial_second polynomial_natEqual)
    (polynomial_constant true)
    (polynomial_composition (polynomial_pair (polynomial_constant 0) polynomial_defectCount)
      polynomial_less)

def positiveRow (z : ReturnInput×ℕ) : Bool :=
  (indices z.1).all (fun j => positiveEntry (z.1,(z.2,j)))

def positiveRowRealizer : Realizer positiveRow :=
  (composition (composition (pair identity (composition first indicesRealizer))
    (mapWith (composition (pair (composition first first)
      (pair (composition first second) second)) positiveEntryRealizer))) all).congr (by
        intro z
        simp only [Function.comp_apply,List.all_map,Function.comp_def,id_eq,positiveRow])

lemma polynomial_positiveRow : PolynomialTime positiveRowRealizer := by
  unfold positiveRowRealizer
  apply polynomial_congr
  exact polynomial_composition (polynomial_composition
    (polynomial_pair polynomial_identity (polynomial_composition polynomial_first polynomial_indices))
    (polynomial_mapWith (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first)
      (polynomial_pair (polynomial_composition polynomial_first polynomial_second) polynomial_second))
      polynomial_positiveEntry))) polynomial_all

def positiveCounts (z : ReturnInput) : Bool :=
  decide (0<plainCountCode z) && (indices z).all (fun i => positiveRow (z,i))

def positiveCountsRealizer : Realizer positiveCounts :=
  (composition (pair (composition (pair (constant 0) plainCountRealizer) less)
    (composition (composition (pair identity indicesRealizer) (mapWith positiveRowRealizer)) all))
      boolAnd).congr (by
        intro z
        simp only [Function.comp_apply,List.all_map,Function.comp_def,id_eq,positiveCounts])

theorem polynomial_positiveCounts : PolynomialTime positiveCountsRealizer := by
  unfold positiveCountsRealizer
  apply polynomial_congr
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair (polynomial_constant 0) polynomial_plainCount) polynomial_less)
    (polynomial_composition (polynomial_composition
      (polynomial_pair polynomial_identity polynomial_indices)
      (polynomial_mapWith polynomial_positiveRow)) polynomial_all)) polynomial_boolAnd

lemma positiveCounts_iff (z : ReturnInput) :
    positiveCounts z=true ↔ 0<plainCountCode z ∧
      ∀ i∈indices z,∀ j∈indices z,i=j ∨ 0<defectCountCode (z,(i,j)) := by
  unfold positiveCounts
  rw [Bool.and_eq_true]
  constructor
  · rintro ⟨hp,h⟩
    refine ⟨of_decide_eq_true hp,fun i hi j hj => ?_⟩
    have hr : positiveRow (z,i)=true := List.all_eq_true.mp h i hi
    have he : positiveEntry (z,(i,j))=true := List.all_eq_true.mp hr j hj
    exact of_decide_eq_true he
  · rintro ⟨hp,h⟩
    refine ⟨decide_eq_true hp,List.all_eq_true.mpr (fun i hi => ?_)⟩
    apply List.all_eq_true.mpr
    intro j hj
    exact decide_eq_true (h i hi j hj)

noncomputable section
open TwoLiftStates
variable {I J : Type} [Fintype I] [Fintype J]
variable (A : Instance I J) {p m : ℕ} (g : Fin p ≃ Labels A)
  (e : (Labels A×Bool) ≃ Fin m)

def matrixCode (w : Fin p → Fin p → TreeFraction.Fraction) : FractionMatrix :=
  List.ofFn (fun i => List.ofFn (w i))

lemma readEntry_code (w : Fin p → Fin p → TreeFraction.Fraction) (i j : Fin p) :
    readEntry (matrixCode w,(i.val,j.val))=w i j := by
  simp only [readEntry,matrixCode,List.getD_eq_getElem?_getD,List.getElem?_ofFn,
    i.isLt,j.isLt,dite_true,Option.getD_some,Fin.eta]

theorem updateEntry_code (states : List (Set (Labels A×Bool)))
    (w : Fin p → Fin p → TreeFraction.Fraction) (i j : Fin p) :
    updateEntry (((orderedCatalog A g e,states.map (encodeSet e)),matrixCode w),(i.val,j.val))=
      updateCode (((orderedCatalog A g e,states.map (encodeSet e)),(i.val,j.val)),w i j) := by
  simp only [updateEntry,readEntry_code]

lemma positiveCounts_code (states : List (Set (Labels A×Bool))) :
    positiveCounts (orderedCatalog A g e,states.map (encodeSet e))=true ↔
      CountsPositive A states := by
  have he : positiveCounts (orderedCatalog A g e,states.map (encodeSet e))=true ↔
      0<plainCount A states ∧ ∀ i j : Fin p,i≠j →
        0<defectCount A states (pair (g i)) (pair (g j)) := by
    rw [positiveCounts_iff,plainCount_code A g e states]
    have hi : indices (orderedCatalog A g e,states.map (encodeSet e))=List.range p := by
      simp only [indices,orderedCatalog,List.length_ofFn]
    rw [hi]
    simp only [List.mem_range]
    constructor
    · rintro ⟨hp,h⟩
      refine ⟨hp,fun i j hij => ?_⟩
      have hh := h i.val i.isLt j.val j.isLt
      have hn : i.val≠j.val := fun h => hij (Fin.ext h)
      simp only [hn,false_or] at hh
      rw [defectCount_code A g e states i j] at hh
      exact hh
    · rintro ⟨hp,h⟩
      refine ⟨hp,fun i hi j hj => ?_⟩
      by_cases hij : i=j
      · exact Or.inl hij
      · right
        have hh := h ⟨i,hi⟩ ⟨j,hj⟩ (fun he => hij (congrArg Fin.val he))
        rw [←defectCount_code A g e states ⟨i,hi⟩ ⟨j,hj⟩] at hh
        exact hh
  rw [he]
  unfold CountsPositive
  constructor
  · rintro ⟨hp,h⟩
    refine ⟨hp,fun a ha b hb hab => ?_⟩
    obtain ⟨a',_,rfl⟩ := List.mem_map.mp ha
    obtain ⟨b',_,rfl⟩ := List.mem_map.mp hb
    obtain ⟨i,rfl⟩ := g.surjective a'
    obtain ⟨j,rfl⟩ := g.surjective b'
    exact h i j (fun he => hab (congrArg (fun k => pair (g k)) he))
  · rintro ⟨hp,h⟩
    refine ⟨hp,fun i j hij => ?_⟩
    exact h _ (pair_mem _) _ (pair_mem _)
      (fun he => hij (g.injective (pair_injective he)))

/-- The executable update contains exactly one entry for every ordered
pair of labels, in the same order as the executable proposal catalog. -/
theorem updateMatrix_code (states : List (Set (Labels A×Bool)))
    (w : Fin p → Fin p → TreeFraction.Fraction) :
    updateMatrix ((orderedCatalog A g e,states.map (encodeSet e)),matrixCode w)=
      matrixCode (fun i j => updateCode
        (((orderedCatalog A g e,states.map (encodeSet e)),(i.val,j.val)),w i j)) := by
  unfold updateMatrix matrixCode
  have hi : indices (orderedCatalog A g e,states.map (encodeSet e))=List.range p := by
    simp only [indices,orderedCatalog,List.length_ofFn]
  rw [hi]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,List.length_ofFn]
  · intro i hi' _
    have hip : i<p := by simpa only [List.length_map,List.length_range] using hi'
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
    unfold updateRow
    rw [hi]
    apply List.ext_getElem
    · simp only [List.length_map,List.length_range,List.length_ofFn]
    · intro j hj' _
      have hjp : j<p := by simpa only [List.length_map,List.length_range] using hj'
      simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn,rowEntry]
      exact updateEntry_code A g e states w ⟨i,hip⟩ ⟨j,hjp⟩

end
end ContingencyTables.CompanionMultiplierMatrixProgram

end OAI
