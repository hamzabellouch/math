import OAI.Combinatorics.ContingencyTables.Sampling.ProfileExchangeProgram
import OAI.Combinatorics.MatchingCount.Machines.TreeFiniteCollections

namespace OAI

/-! # A polynomial binary program listing all coordinate exchanges -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial

def profileIndices : Realizer (fun xs : List ℕ => List.range xs.length) :=
  composition listLength range

lemma polynomial_profileIndices : PolynomialTime profileIndices := by
  apply polynomial_boundedRange polynomial_listLength X
  intro xs
  simpa only [Polynomial.eval_X] using list_length_le_weight xs

def exchangeRow (z : List ℕ×ℕ) : List (List ℕ) :=
  (List.range z.1.length).map (fun j => listExchange (z.1,(z.2,j)))

def exchangeRowRealizer : Realizer exchangeRow := by
  let E : Realizer (fun z : (List ℕ×ℕ)×ℕ => listExchange (z.1.1,(z.1.2,z.2))) :=
    composition (pair (composition first first) (pair (composition first second) second))
      listExchangeRealizer
  exact composition (pair identity (composition first profileIndices)) (mapWith E)

lemma polynomial_exchangeRow : PolynomialTime exchangeRowRealizer := by
  unfold exchangeRowRealizer
  exact polynomial_composition
    (polynomial_pair polynomial_identity (polynomial_composition polynomial_first polynomial_profileIndices))
    (polynomial_mapWith (polynomial_composition
      (polynomial_pair (polynomial_composition polynomial_first polynomial_first)
        (polynomial_pair (polynomial_composition polynomial_first polynomial_second) polynomial_second))
      polynomial_listExchange))

def allExchanges (xs : List ℕ) : List (List ℕ) :=
  ((List.range xs.length).map (fun i => exchangeRow (xs,i))).flatten

def allExchangesRealizer : Realizer allExchanges :=
  composition (composition (pair identity profileIndices) (mapWith exchangeRowRealizer)) flatten

theorem polynomial_allExchanges : PolynomialTime allExchangesRealizer :=
  polynomial_composition (polynomial_composition
    (polynomial_pair polynomial_identity polynomial_profileIndices)
    (polynomial_mapWith polynomial_exchangeRow)) polynomial_flatten

lemma exchangeRow_length (z : List ℕ×ℕ) : (exchangeRow z).length=z.1.length := by
  simp only [exchangeRow,List.length_map,List.length_range]

theorem allExchanges_length (xs : List ℕ) : (allExchanges xs).length=xs.length^2 := by
  simp only [allExchanges,List.length_flatten,List.map_map,Function.comp_def,exchangeRow_length]
  simp [pow_two]

/-- Every generated vector is an actual ordered-coordinate update,
and every such update occurs. Duplicate profiles can be removed later. -/
theorem mem_allExchanges_ofFn {n : ℕ} (v : Fin n → ℕ) (xs : List ℕ) :
    xs ∈ allExchanges (List.ofFn v) ↔
      ∃ i j : Fin n,xs=List.ofFn (IntegerWeightedTransport.exchangeTarget v i j) := by
  simp only [allExchanges,List.mem_flatten,List.mem_map]
  constructor
  · rintro ⟨ys,⟨i,hi,rfl⟩,hxs⟩
    obtain ⟨j,hj,hxs⟩ := List.mem_map.mp hxs
    have hi' : i<n := by simpa only [List.mem_range,List.length_ofFn] using hi
    have hj' : j<n := by simpa only [List.mem_range,List.length_ofFn] using hj
    refine ⟨⟨i,hi'⟩,⟨j,hj'⟩,?_⟩
    exact hxs.symm.trans (listExchange_ofFn v ⟨i,hi'⟩ ⟨j,hj'⟩)
  · rintro ⟨i,j,rfl⟩
    refine ⟨exchangeRow (List.ofFn v,i.val),⟨i.val,?_,rfl⟩,?_⟩
    · simpa only [List.mem_range,List.length_ofFn] using i.isLt
    · exact List.mem_map.mpr ⟨j.val,by simpa only [List.mem_range,List.length_ofFn] using j.isLt,
        listExchange_ofFn v i j⟩

end ContingencyTables.ProfilePrograms

end OAI
