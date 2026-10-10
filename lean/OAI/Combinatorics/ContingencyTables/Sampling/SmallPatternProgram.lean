import OAI.Combinatorics.ContingencyTables.Sampling.SmallPatternArithmetic
import OAI.Combinatorics.ContingencyTables.Sampling.SmallCellCatalogProgram

namespace OAI

/-! # Polynomial tests for the two allowed small-profile patterns -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial

abbrev PatternData := (List ℕ×List ℕ)×ℕ
abbrev LabelledPattern := PatternData×(ℕ×ℕ)

def pairSum (z : PatternData×ℕ) : ℕ := z.1.1.1.getD z.2 0+z.1.1.2.getD z.2 0

def pairSumRealizer : Realizer pairSum :=
  composition (pair
    (composition (pair (composition (composition first first) first) second) (getDFast 0))
    (composition (pair (composition (composition first first) second) second) (getDFast 0))) add

lemma polynomial_pairSum : PolynomialTime pairSumRealizer := by
  unfold pairSumRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
      polynomial_second) (polynomial_getDFast 0))
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      polynomial_second) (polynomial_getDFast 0))) polynomial_add

def indexIndicator : Realizer (fun z : ℕ×ℕ => if z.1=z.2 then (1:ℕ) else 0) :=
  (choose natEqual (constant 1) (constant 0)).congr (by
    intro z; simp only [decide_eq_true_eq])

lemma polynomial_indexIndicator : PolynomialTime indexIndicator := by
  unfold indexIndicator
  exact polynomial_congr _ (polynomial_choose polynomial_natEqual
    (polynomial_constant 1) (polynomial_constant 0))

def patternIndices : Realizer (fun z : PatternData => List.range z.1.1.length) :=
  composition (composition (composition first first) listLength) range

lemma polynomial_patternIndices : PolynomialTime patternIndices := by
  apply polynomial_boundedRange
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_listLength) X
  intro z
  have hw : weight z.1.1≤weight z := by
    rcases z with ⟨⟨xs,ys⟩,U⟩
    simp only [weight_prod]
    omega
  simpa only [Function.comp_apply,eval_X] using (list_length_le_weight z.1.1).trans hw

def balancedAt (z : PatternData×ℕ) : Bool := decide (pairSum z=z.1.2)

def balancedAtRealizer : Realizer balancedAt :=
  composition (pair pairSumRealizer (composition first second)) natEqual

lemma polynomial_balancedAt : PolynomialTime balancedAtRealizer :=
  polynomial_composition (polynomial_pair polynomial_pairSum
    (polynomial_composition polynomial_first polynomial_second)) polynomial_natEqual

def balancedTest (z : PatternData) : Bool :=
  (List.range z.1.1.length).all (fun i => balancedAt (z,i))

def balancedTestRealizer : Realizer balancedTest :=
  (composition (composition (pair identity patternIndices) (mapWith balancedAtRealizer)) all).congr
    (by intro z; simp only [Function.comp_apply,List.all_map,Function.comp_def,id_eq,balancedTest])

lemma polynomial_balancedTest : PolynomialTime balancedTestRealizer :=
  polynomial_congr _ (polynomial_composition (polynomial_composition
    (polynomial_pair polynomial_identity polynomial_patternIndices)
    (polynomial_mapWith polynomial_balancedAt)) polynomial_all)

def defectAt (z : LabelledPattern×ℕ) : Bool :=
  decide (pairSum (z.1.1,z.2)+(if z.2=z.1.2.1 then 1 else 0)=
    z.1.1.2+(if z.2=z.1.2.2 then 1 else 0))

def defectAtRealizer : Realizer defectAt :=
  composition (pair
    (composition (pair
      (composition (pair (composition first first) second) pairSumRealizer)
      (composition (pair second (composition (composition first second) first)) indexIndicator)) add)
    (composition (pair (composition (composition first first) second)
      (composition (pair second (composition (composition first second) second)) indexIndicator)) add))
    natEqual

lemma polynomial_defectAt : PolynomialTime defectAtRealizer := by
  unfold defectAtRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_pair
        (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_pairSum)
      (polynomial_composition (polynomial_pair polynomial_second
        (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_first))
        polynomial_indexIndicator)) polynomial_add)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      (polynomial_composition (polynomial_pair polynomial_second
        (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_second))
        polynomial_indexIndicator)) polynomial_add)) polynomial_natEqual

def defectTest (z : LabelledPattern) : Bool :=
  decide (z.2.1≠z.2.2) && (List.range z.1.1.1.length).all (fun i => defectAt (z,i))

def defectTestRealizer : Realizer defectTest :=
  (composition (pair
    (composition (composition second natEqual) boolNot)
    (composition (composition (pair identity (composition first patternIndices))
      (mapWith defectAtRealizer)) all)) boolAnd).congr (by
        intro z
        apply Bool.eq_iff_iff.mpr
        simp only [Function.comp_apply,Bool.and_eq_true,Bool.not_eq_true',
          decide_eq_false_iff_not,defectTest,decide_eq_true_eq,List.all_map,Function.comp_def,id_eq])

lemma polynomial_defectTest : PolynomialTime defectTestRealizer := by
  unfold defectTestRealizer
  exact polynomial_congr _ (polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_second polynomial_natEqual) polynomial_boolNot)
    (polynomial_composition (polynomial_composition
      (polynomial_pair polynomial_identity (polynomial_composition polynomial_first polynomial_patternIndices))
      (polynomial_mapWith polynomial_defectAt)) polynomial_all)) polynomial_boolAnd)

def patternTest (z : PatternData) : Bool :=
  balancedTest z || (cellPairs (z.1.1,z.1.1)).any (fun st => defectTest (z,st))

def patternTestRealizer : Realizer patternTest :=
  (composition (pair balancedTestRealizer
    (composition (composition (pair identity
      (composition (pair (composition first first) (composition first first)) cellPairsRealizer))
      (mapWith defectTestRealizer)) any)) boolOr).congr (by
        intro z
        simp only [Function.comp_apply,List.any_map,Function.comp_def,id_eq,patternTest])

theorem polynomial_patternTest : PolynomialTime patternTestRealizer := by
  unfold patternTestRealizer
  exact polynomial_congr _ (polynomial_composition (polynomial_pair polynomial_balancedTest
    (polynomial_composition (polynomial_composition (polynomial_pair polynomial_identity
      (polynomial_composition (polynomial_pair
        (polynomial_composition polynomial_first polynomial_first)
        (polynomial_composition polynomial_first polynomial_first)) polynomial_cellPairs))
      (polynomial_mapWith polynomial_defectTest)) polynomial_any)) polynomial_boolOr)

lemma pairSum_ofFn {n : ℕ} (x y : Fin n → ℕ) (U : ℕ) (i : Fin n) :
    pairSum (((List.ofFn x,List.ofFn y),U),i.val)=x i+y i := by
  simp only [pairSum,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp only [i.isLt,dite_true,Option.getD_some]

theorem balancedTest_ofFn {n : ℕ} (x y : Fin n → ℕ) (U : ℕ) :
    balancedTest ((List.ofFn x,List.ofFn y),U)=true ↔ ∀ i,x i+y i=U := by
  simp only [balancedTest,List.all_eq_true,List.mem_range,List.length_ofFn,balancedAt,
    decide_eq_true_eq]
  constructor
  · intro h i
    simpa only [pairSum_ofFn] using h i.val i.isLt
  · intro h i hi
    exact (pairSum_ofFn x y U ⟨i,hi⟩).trans (h ⟨i,hi⟩)

theorem defectTest_ofFn {n : ℕ} (x y : Fin n → ℕ) (U : ℕ) (s t : Fin n) :
    defectTest (((List.ofFn x,List.ofFn y),U),(s.val,t.val))=true ↔
      s≠t ∧ ∀ i,x i+y i+(if i=s then 1 else 0)=U+(if i=t then 1 else 0) := by
  simp only [defectTest,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,
    List.mem_range,List.length_ofFn,defectAt]
  constructor
  · rintro ⟨hne,h⟩
    refine ⟨fun he => hne (congrArg Fin.val he),fun i => ?_⟩
    simpa only [pairSum_ofFn,Fin.ext_iff] using h i.val i.isLt
  · rintro ⟨hne,h⟩
    refine ⟨fun he => hne (Fin.ext he),fun i hi => ?_⟩
    rw [show pairSum (((List.ofFn x,List.ofFn y),U),i)=x ⟨i,hi⟩+y ⟨i,hi⟩ from
      pairSum_ofFn x y U ⟨i,hi⟩]
    simpa only [Fin.ext_iff] using h ⟨i,hi⟩

theorem patternTest_ofFn {n : ℕ} (x y : Fin n → ℕ) (U : ℕ) :
    patternTest ((List.ofFn x,List.ofFn y),U)=true ↔
      (∀ i,x i+y i=U) ∨ ∃ s t : Fin n,s≠t ∧
        ∀ i,x i+y i+(if i=s then 1 else 0)=U+(if i=t then 1 else 0) := by
  simp only [patternTest,Bool.or_eq_true,balancedTest_ofFn,List.any_eq_true]
  constructor
  · rintro (h|⟨⟨s,t⟩,hst,h⟩)
    · exact Or.inl h
    · have hb := (mem_cellPairs (List.ofFn x) (List.ofFn x) s t).mp hst
      simp only [List.length_ofFn] at hb
      exact Or.inr ⟨⟨s,hb.1⟩,⟨t,hb.2⟩,(defectTest_ofFn x y U _ _).mp h⟩
  · rintro (h|⟨s,t,h⟩)
    · exact Or.inl h
    · refine Or.inr ⟨(s.val,t.val),?_,(defectTest_ofFn x y U s t).mpr h⟩
      apply (mem_cellPairs (List.ofFn x) (List.ofFn x) _ _).mpr
      simpa only [List.length_ofFn] using And.intro s.isLt t.isLt

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.SmallGraphProfiles
open scoped Classical
open SmallContextCoordinates PhysicalCompletionFibres ProfilePrograms

noncomputable section
universe u
variable {I J : Type u} [LinearOrder I] [LinearOrder J]

/-- The binary list test recognizes exactly the manuscript's profile
patterns on the common small-cell box. -/
theorem patternTest_views (small : I → J → Bool) (B : I → J → ℕ)
    {n : ℕ} (e : Fin n ≃ Cells small) (z : SmallProfile small) (U : ℕ)
    (hU : ∀ a : Cells small,B a.val.1 a.val.2=U)
    (hb : ∀ a : Cells small,z (a,true)≤B a.val.1 a.val.2) :
    patternTest ((viewList small e z false,viewList small e z true),U)=true ↔
      Pattern small B z := by
  rw [viewList,viewList,patternTest_ofFn,pattern_iff_cellSums small B z hb]
  constructor
  · rintro (h|⟨s,t,hne,h⟩)
    · left
      intro a
      simpa only [Equiv.apply_symm_apply,hU] using h (e.symm a)
    · right
      refine ⟨e s,e t,fun he => hne (e.injective he),?_⟩
      intro a
      have hs : e.symm a=s ↔ a=e s := by
        constructor
        · intro he; rw [←he,Equiv.apply_symm_apply]
        · intro he; rw [he,Equiv.symm_apply_apply]
      have ht : e.symm a=t ↔ a=e t := by
        constructor
        · intro he; rw [←he,Equiv.apply_symm_apply]
        · intro he; rw [he,Equiv.symm_apply_apply]
      simpa only [Equiv.apply_symm_apply,hU,hs,ht] using h (e.symm a)
  · rintro (h|⟨s,t,hne,h⟩)
    · left
      intro i
      simpa only [hU] using h (e i)
    · right
      refine ⟨e.symm s,e.symm t,fun he => hne (e.symm.injective he),?_⟩
      intro i
      have hs : e i=s ↔ i=e.symm s := by
        constructor
        · intro he; rw [←he,Equiv.symm_apply_apply]
        · intro he; rw [he,Equiv.apply_symm_apply]
      have ht : e i=t ↔ i=e.symm t := by
        constructor
        · intro he; rw [←he,Equiv.symm_apply_apply]
        · intro he; rw [he,Equiv.apply_symm_apply]
      simpa only [hU,hs,ht] using h (e i)

end
end ContingencyTables.SmallGraphProfiles

end OAI
