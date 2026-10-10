import OAI.Combinatorics.ContingencyTables.Sampling.SmallProfileFlatCode
import OAI.Combinatorics.ContingencyTables.Sampling.SmallCellCatalogProgram

namespace OAI

/-! # Enumerating all directed unit exchanges of a stored profile -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def positiveExchangeTest (z : List ℕ×(ℕ×ℕ)) : Bool :=
  decide (z.2.1≠z.2.2 ∧ 0<z.1.getD z.2.2 0)

def positiveExchangeTestRealizer : Realizer positiveExchangeTest :=
  (composition (pair (composition (composition second natEqual) boolNot)
    (composition (pair (constant 0)
      (composition (pair first (composition second second)) (getDFast 0))) less)) boolAnd).congr (by
        intro z
        apply Bool.eq_iff_iff.mpr
        simp only [Function.comp_apply,Bool.and_eq_true,Bool.not_eq_true',
          decide_eq_false_iff_not,decide_eq_true_eq,positiveExchangeTest])

lemma polynomial_positiveExchangeTest : PolynomialTime positiveExchangeTestRealizer :=
  polynomial_congr _ (polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_second polynomial_natEqual)
      polynomial_boolNot)
    (polynomial_composition (polynomial_pair (polynomial_constant 0)
      (polynomial_composition (polynomial_pair polynomial_first
        (polynomial_composition polynomial_second polynomial_second)) (polynomial_getDFast 0)))
      polynomial_less)) polynomial_boolAnd)

def positiveExchangeIndices (xs : List ℕ) : List (ℕ×ℕ) :=
  (cellPairs (xs,xs)).filter (fun ij => positiveExchangeTest (xs,ij))

def positiveExchangeIndicesRealizer : Realizer positiveExchangeIndices :=
  composition (pair identity (composition (pair identity identity) cellPairsRealizer))
    (filterWith positiveExchangeTestRealizer)

lemma polynomial_positiveExchangeIndices : PolynomialTime positiveExchangeIndicesRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition (polynomial_pair polynomial_identity polynomial_identity)
      polynomial_cellPairs)) (polynomial_filterWith polynomial_positiveExchangeTest)

lemma mem_positiveExchangeIndices (xs : List ℕ) (i j : ℕ) :
    (i,j)∈positiveExchangeIndices xs ↔
      i<xs.length ∧ j<xs.length ∧ i≠j ∧ 0<xs.getD j 0 := by
  simp only [positiveExchangeIndices,List.mem_filter,mem_cellPairs,positiveExchangeTest,
    decide_eq_true_eq]
  tauto

def codeExchangeList (v : List ℕ×List ℕ) : List (List ℕ×List ℕ) :=
  (positiveExchangeIndices (flattenViews v)).map (fun ij => codeExchange (v,ij))

def codeExchangeListRealizer : Realizer codeExchangeList :=
  composition (pair identity (composition flattenViewsRealizer positiveExchangeIndicesRealizer))
    (mapWith codeExchangeRealizer)

theorem polynomial_codeExchangeList : PolynomialTime codeExchangeListRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition polynomial_flattenViews polynomial_positiveExchangeIndices))
    (polynomial_mapWith polynomial_codeExchange)

lemma codeExchangeList_length (v : List ℕ×List ℕ) :
    (codeExchangeList v).length≤(v.1.length+v.2.length)^2 := by
  have h := List.length_filter_le (fun ij => positiveExchangeTest (flattenViews v,ij))
    (cellPairs (flattenViews v,flattenViews v))
  simpa only [codeExchangeList,List.length_map,positiveExchangeIndices,cellPairs,
    List.length_range,flattenViews,List.length_append,pow_two] using h

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.SmallGraphProfiles
open scoped Classical
open SmallContextCoordinates PhysicalCompletionFibres FirstPaperProfiles ProfilePrograms
open IntegerWeightedTransport

noncomputable section
variable {m n q : ℕ} (small : Fin m → Fin n → Bool) (e : Fin q ≃ Cells small)

private lemma flat_getD (z : SmallProfile small) (i : Fin (q+q)) :
    (flattenViews (profileCode small e z)).getD i.val 0=z (flatViewEquiv small e i) := by
  rw [flatten_profileCode]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,i.isLt,dite_true,Option.getD_some,Fin.eta]

theorem mem_codeExchangeList (z : SmallProfile small) (w : List ℕ×List ℕ) :
    w∈codeExchangeList (profileCode small e z) ↔
      ∃ i j : Cells small×Bool,i≠j ∧ 0<z j ∧
        w=profileCode small e (exchangeTarget z i j) := by
  simp only [codeExchangeList,List.mem_map]
  constructor
  · rintro ⟨⟨i,j⟩,hij,hw⟩
    have hh := (mem_positiveExchangeIndices _ i j).mp hij
    have hi : i<q+q := by
      simpa only [flattenViews,profileCode,viewList,List.length_append,List.length_ofFn] using hh.1
    have hj : j<q+q := by
      simpa only [flattenViews,profileCode,viewList,List.length_append,List.length_ofFn] using hh.2.1
    let a : Fin (q+q) := ⟨i,hi⟩
    let b : Fin (q+q) := ⟨j,hj⟩
    refine ⟨flatViewEquiv small e a,flatViewEquiv small e b,?_,?_,?_⟩
    · intro he
      exact hh.2.2.1 (congrArg Fin.val ((flatViewEquiv small e).injective he))
    · rw [←flat_getD small e z b]
      exact hh.2.2.2
    · exact hw.symm.trans (codeExchange_eq small e z a b)
  · rintro ⟨a,b,hab,hb,rfl⟩
    let i := (flatViewEquiv small e).symm a
    let j := (flatViewEquiv small e).symm b
    refine ⟨(i.val,j.val),?_,?_⟩
    · apply (mem_positiveExchangeIndices _ _ _).mpr
      refine ⟨?_,?_,?_,?_⟩
      · simpa only [flattenViews,profileCode,viewList,List.length_append,List.length_ofFn] using i.isLt
      · simpa only [flattenViews,profileCode,viewList,List.length_append,List.length_ofFn] using j.isLt
      · intro he
        have he' : i=j := Fin.ext he
        exact hab ((flatViewEquiv small e).symm.injective he')
      · simpa only [flat_getD small e z j,j,Equiv.apply_symm_apply] using hb
    · simpa only [i,j,Equiv.apply_symm_apply] using codeExchange_eq small e z i j

end
end ContingencyTables.SmallGraphProfiles

end OAI
