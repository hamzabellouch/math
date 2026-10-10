import OAI.Combinatorics.ContingencyTables.Sampling.SmallMarginSemantics
import OAI.Combinatorics.ContingencyTables.Sampling.SmallBoundsProgram

namespace OAI

/-! # A polynomial binary validator for the positive profile space -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

abbrev ProfileCheckData := ((List (ℕ×ℕ)×(List ℕ×List ℕ))×(List ℕ×List ℕ))×ℕ

def profileViews : Realizer (fun z : ProfileCheckData => z.1.1.2) :=
  composition (composition first first) second

def profileCatalog : Realizer (fun z : ProfileCheckData => z.1.1.1) :=
  composition (composition first first) first

def profileMargins : Realizer (fun z : ProfileCheckData => z.1.2) :=
  composition first second

lemma polynomial_profileViews : PolynomialTime profileViews :=
  polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second

lemma polynomial_profileCatalog : PolynomialTime profileCatalog :=
  polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first

lemma polynomial_profileMargins : PolynomialTime profileMargins :=
  polynomial_composition polynomial_first polynomial_second

def profileView (row : Bool) : Realizer (fun z : ProfileCheckData =>
    if row then z.1.1.2.1 else z.1.1.2.2) :=
  choose (constant row) (composition profileViews first) (composition profileViews second)

lemma polynomial_profileView (row : Bool) : PolynomialTime (profileView row) :=
  polynomial_choose (polynomial_constant row)
    (polynomial_composition polynomial_profileViews polynomial_first)
    (polynomial_composition polynomial_profileViews polynomial_second)

def profileBound (row : Bool) : Realizer (fun z : ProfileCheckData =>
    boundedValues (z.2,if row then z.1.1.2.1 else z.1.1.2.2)) :=
  composition (pair second (profileView row)) boundedValuesRealizer

lemma polynomial_profileBound (row : Bool) : PolynomialTime (profileBound row) :=
  polynomial_composition (polynomial_pair polynomial_second (polynomial_profileView row))
    polynomial_boundedValues

def profileShape (row : Bool) : Realizer (fun z : ProfileCheckData =>
    decide ((if row then z.1.1.2.1 else z.1.1.2.2).length=z.1.1.1.length)) :=
  composition (pair (composition (profileView row) listLength)
    (composition profileCatalog listLength)) natEqual

lemma polynomial_profileShape (row : Bool) : PolynomialTime (profileShape row) :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_profileView row) polynomial_listLength)
    (polynomial_composition polynomial_profileCatalog polynomial_listLength)) polynomial_natEqual

def profilePattern : Realizer (fun z : ProfileCheckData => patternTest (z.1.1.2,z.2)) :=
  composition (pair profileViews second) patternTestRealizer

lemma polynomial_profilePattern : PolynomialTime profilePattern :=
  polynomial_composition (polynomial_pair polynomial_profileViews polynomial_second)
    polynomial_patternTest

def profileColumnView : Realizer (fun z : ProfileCheckData =>
    complementValues (z.2,z.1.1.2.2)) :=
  composition (pair second (composition profileViews second)) complementValuesRealizer

lemma polynomial_profileColumnView : PolynomialTime profileColumnView :=
  polynomial_composition (polynomial_pair polynomial_second
    (polynomial_composition polynomial_profileViews polynomial_second)) polynomial_complementValues

def profileLineData (row : Bool) : Realizer (fun z : ProfileCheckData =>
    (((z.1.1.1,if row then z.1.1.2.1 else complementValues (z.2,z.1.1.2.2)),z.1.2),z.2)) :=
  pair (pair (pair profileCatalog
    (choose (constant row) (profileView true) profileColumnView)) profileMargins) second

lemma polynomial_profileLineData (row : Bool) : PolynomialTime (profileLineData row) :=
  polynomial_pair (polynomial_pair (polynomial_pair polynomial_profileCatalog
    (polynomial_choose (polynomial_constant row) (polynomial_profileView true)
      polynomial_profileColumnView)) polynomial_profileMargins) polynomial_second

def profileLineTest (row : Bool) : Realizer (fun z : ProfileCheckData =>
    validMargins row (((z.1.1.1,
      if row then z.1.1.2.1 else complementValues (z.2,z.1.1.2.2)),z.1.2),z.2)) :=
  composition (profileLineData row) (validMarginsRealizer row)

lemma polynomial_profileLineTest (row : Bool) : PolynomialTime (profileLineTest row) :=
  polynomial_composition (polynomial_profileLineData row) (polynomial_validMargins row)

def profileTest (z : ProfileCheckData) : Bool :=
  decide (z.1.1.2.1.length=z.1.1.1.length) &&
    (decide (z.1.1.2.2.length=z.1.1.1.length) &&
    (boundedValues (z.2,z.1.1.2.1) &&
    (boundedValues (z.2,z.1.1.2.2) &&
    (patternTest (z.1.1.2,z.2) &&
    (validMargins true (((z.1.1.1,z.1.1.2.1),z.1.2),z.2) &&
      validMargins false (((z.1.1.1,complementValues (z.2,z.1.1.2.2)),z.1.2),z.2))))))

def profileTestRealizer : Realizer profileTest :=
  composition (pair (profileShape true)
    (composition (pair (profileShape false)
    (composition (pair (profileBound true)
    (composition (pair (profileBound false)
    (composition (pair profilePattern
    (composition (pair (profileLineTest true) (profileLineTest false)) boolAnd)) boolAnd))
      boolAnd)) boolAnd)) boolAnd)) boolAnd

theorem polynomial_profileTest : PolynomialTime profileTestRealizer :=
  polynomial_composition (polynomial_pair (polynomial_profileShape true)
    (polynomial_composition (polynomial_pair (polynomial_profileShape false)
    (polynomial_composition (polynomial_pair (polynomial_profileBound true)
    (polynomial_composition (polynomial_pair (polynomial_profileBound false)
    (polynomial_composition (polynomial_pair polynomial_profilePattern
    (polynomial_composition (polynomial_pair (polynomial_profileLineTest true)
      (polynomial_profileLineTest false)) polynomial_boolAnd)) polynomial_boolAnd))
      polynomial_boolAnd)) polynomial_boolAnd)) polynomial_boolAnd)) polynomial_boolAnd

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.SmallGraphProfiles
open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open PaddedCompletions ProfilePrograms FirstPaperPhysicalMarginal CompletionCounts

noncomputable section
variable {m n q : ℕ}

theorem profileTest_iff (r : Fin m → ℕ) (c : Fin n → ℕ)
    (htotal : (∑ i,r i)=∑ j,c j) (e : Fin q ≃ Cells (paperSmall r c))
    (z : SmallProfile (paperSmall r c)) :
    profileTest (((cellCatalog (paperSmall r c) e,
      (viewList (paperSmall r c) e z false,viewList (paperSmall r c) e z true)),
      (List.ofFn r,List.ofFn c)),(dimensionAllowance (I := Fin m) (J := Fin n))^20)=true ↔
        ProfileFeasible r c z := by
  let small := paperSmall r c
  let B := stateCapacity r c
  let U := (dimensionAllowance (I := Fin m) (J := Fin n))^20
  have hU (a : Cells small) : B a.val.1 a.val.2=U :=
    stateCapacity_small r c _ _ a.property
  have hb : (∀ a,z a≤U) ↔ ∀ a,z a≤B a.1.val.1 a.1.val.2 := by
    simp only [hU]
  simp only [profileTest,Bool.and_eq_true,cellCatalog,viewList,List.length_ofFn,
    decide_true,true_and]
  change (boundedValues (U,viewList small e z false)=true ∧
    (boundedValues (U,viewList small e z true)=true ∧
    (patternTest ((viewList small e z false,viewList small e z true),U)=true ∧
    (validMargins true (((cellCatalog small e,viewList small e z false),
      (List.ofFn r,List.ofFn c)),U)=true ∧
    validMargins false (((cellCatalog small e,complementValues (U,viewList small e z true)),
      (List.ofFn r,List.ofFn c)),U)=true)))) ↔ _
  constructor
  · rintro ⟨hx,hy,hp,hr,hc⟩
    have hbound : ∀ a,z a≤U := (boundedValues_views small e z U).mp (by simpa using And.intro hx hy)
    apply profileFeasible_of_lineTests r c htotal z (hb.mp hbound)
    · exact (patternTest_views small B e z U hU (fun a => hb.mp hbound (a,true))).mp hp
    · exact (validRows_iff small e z r c U).mp hr
    · exact (validColumns_iff small e B z r c U hU).mp hc
  · intro h
    have hbound := hb.mpr h.bounded
    have hh := (boundedValues_views small e z U).mpr hbound
    have hxy := Bool.and_eq_true_iff.mp hh
    have hl := profileFeasible_lineTests r c z h
    refine ⟨hxy.1,hxy.2,?_,?_,?_⟩
    · exact (patternTest_views small B e z U hU (fun a => h.bounded (a,true))).mpr h.pattern
    · exact (validRows_iff small e z r c U).mpr hl.1
    · exact (validColumns_iff small e B z r c U hU).mpr hl.2

end
end ContingencyTables.SmallGraphProfiles

end OAI
