import OAI.Combinatorics.ContingencyTables.Sampling.SmallViewLookupProgram
import OAI.Combinatorics.MatchingCount.Complexity.TreePolynomialSums

namespace OAI

/-! # Binary row and column sums of the sparse stored view -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial
open scoped BigOperators

abbrev LineData := ((List (ℕ×ℕ)×List ℕ)×List ℕ)×ℕ

def lineEntry (row : Bool) (z : LineData×ℕ) : ℕ :=
  lookupView (z.1.1.1,if row then (z.1.2,z.2) else (z.2,z.1.2))

def lineEntryRealizer (row : Bool) : Realizer (lineEntry row) :=
  composition (pair (composition (composition first first) first)
    (choose (constant row) (pair (composition first second) second)
      (pair second (composition first second)))) lookupViewRealizer

lemma polynomial_lineEntry (row : Bool) : PolynomialTime (lineEntryRealizer row) :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
    (polynomial_choose (polynomial_constant row)
      (polynomial_pair (polynomial_composition polynomial_first polynomial_second) polynomial_second)
      (polynomial_pair polynomial_second (polynomial_composition polynomial_first polynomial_second))))
    polynomial_lookupView

def lineIndices : Realizer (fun z : LineData => List.range z.1.2.length) :=
  composition (composition (composition first second) listLength) range

lemma polynomial_lineIndices : PolynomialTime lineIndices := by
  apply polynomial_boundedRange
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
      polynomial_listLength) X
  intro z
  have hw : weight z.1.2≤weight z := by
    rcases z with ⟨⟨lookupData,coords⟩,i⟩
    simp only [weight_prod]
    omega
  simpa only [Function.comp_apply,eval_X] using (list_length_le_weight z.1.2).trans hw

def lineSum (row : Bool) (z : LineData) : ℕ :=
  ((List.range z.1.2.length).map (fun i => lineEntry row (z,i))).sum

def lineSumRealizer (row : Bool) : Realizer (lineSum row) :=
  composition (composition (pair identity lineIndices) (mapWith (lineEntryRealizer row))) listSum

theorem polynomial_lineSum (row : Bool) : PolynomialTime (lineSumRealizer row) :=
  polynomial_composition (polynomial_composition
    (polynomial_pair polynomial_identity polynomial_lineIndices)
    (polynomial_mapWith (polynomial_lineEntry row))) polynomial_listSum

lemma lineSum_eq_sum {n : ℕ} (row : Bool) (z : LineData) (hsize : z.1.2.length=n)
    (f : Fin n → ℕ) (hf : ∀ i,lineEntry row (z,i.val)=f i) :
    lineSum row z=∑ i,f i := by
  unfold lineSum
  have he : (List.range z.1.2.length).map (fun i => lineEntry row (z,i))=List.ofFn f := by
    apply List.ext_getElem
    · simp only [List.length_map,List.length_range,List.length_ofFn,hsize]
    · intro i hi _
      have hin : i<n := by simpa only [List.length_map,List.length_range,hsize] using hi
      simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
      exact hf ⟨i,hin⟩
  rw [he,List.sum_ofFn]

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.SmallGraphProfiles
open scoped BigOperators Classical
open SmallContextCoordinates PhysicalCompletionFibres FirstPaperProfiles ProfilePrograms

noncomputable section
variable {m n q : ℕ} (small : Fin m → Fin n → Bool) (e : Fin q ≃ Cells small)

theorem rowSum_eq (z : SmallProfile small) (b : Bool) (c : Fin n → ℕ) (i : Fin m) :
    lineSum true (((cellCatalog small e,viewList small e z b),List.ofFn c),i.val)=
      ∑ j,smallView small z b i j := by
  apply lineSum_eq_sum true _ List.length_ofFn
  intro j
  exact lookupView_eq small e z b i j

theorem columnSum_eq (z : SmallProfile small) (b : Bool) (r : Fin m → ℕ) (j : Fin n) :
    lineSum false (((cellCatalog small e,viewList small e z b),List.ofFn r),j.val)=
      ∑ i,smallView small z b i j := by
  apply lineSum_eq_sum false _ List.length_ofFn
  intro i
  exact lookupView_eq small e z b i j

end
end ContingencyTables.SmallGraphProfiles

end OAI
