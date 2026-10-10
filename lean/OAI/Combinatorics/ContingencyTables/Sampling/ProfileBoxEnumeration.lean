import OAI.Combinatorics.ContingencyTables.Sampling.ProfileBoxIndex
import OAI.Combinatorics.ContingencyTables.Machines.CompletionEnumerationProgram

namespace OAI

/-! # Executable enumeration of the bounded two-view profile box -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

def profileEnumerationData (z : ProfileCheckData) : GridEnumerationData :=
  (((z.1.1.1++z.1.1.1).map (fun _ => false)),z.2+1)

def profileEnumerationDataRealizer : Realizer profileEnumerationData := by
  let catalog : Realizer (fun z : ProfileCheckData => z.1.1.1) :=
    composition (composition first first) first
  let markers := composition (composition (pair catalog catalog) append) (map (constant false))
  exact pair markers (composition second successor)

lemma polynomial_profileEnumerationData : PolynomialTime profileEnumerationDataRealizer := by
  unfold profileEnumerationDataRealizer
  exact polynomial_pair (polynomial_composition
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first))
      polynomial_append) (polynomial_map (polynomial_constant false)))
    (polynomial_composition polynomial_second polynomial_successor)

def profileBoxViews (z : ProfileCheckData) : List (List ℕ×List ℕ) :=
  (gridWords (profileEnumerationData z)).map (fun word => splitViews (z.1.1.1.length,word))

def profileBoxViewsRealizer : Realizer profileBoxViews := by
  let width : Realizer (fun z : ProfileCheckData => z.1.1.1.length) :=
    composition (composition (composition first first) first) listLength
  let words := composition profileEnumerationDataRealizer gridWordsRealizer
  exact composition (pair width words) (mapWith splitViewsRealizer)

lemma work_profileBoxViews : WorkBound profileBoxViewsRealizer
    (fun z => gridStateCount (profileEnumerationData z)+weight z) := by
  have hp : WorkBound profileEnumerationDataRealizer
      (fun z => gridStateCount (profileEnumerationData z)+weight z) :=
    work_of_polynomial polynomial_profileEnumerationData Polynomial.X (fun z => by simp)
  obtain ⟨p,hp'⟩ := hp
  have hw : WorkBound (composition profileEnumerationDataRealizer gridWordsRealizer)
      (fun z => gridStateCount (profileEnumerationData z)+weight z) := by
    apply work_composition ⟨p,hp'⟩ work_gridWords (Polynomial.X+p)
    intro z
    have h := hp' z
    simp only [Polynomial.eval_add,Polynomial.eval_X]
    change gridStateCount (profileEnumerationData z)+weight (profileEnumerationData z)≤_
    change _≤p.eval (gridStateCount (profileEnumerationData z)+weight z) at h
    omega
  unfold profileBoxViewsRealizer
  apply work_then_polynomial _ (polynomial_mapWith polynomial_splitViews)
  apply work_pair _ hw Polynomial.X (fun z => by simp)
  apply work_of_polynomial _ Polynomial.X (fun z => by simp)
  exact polynomial_composition (polynomial_composition
    (polynomial_composition polynomial_first polynomial_first) polynomial_first)
    polynomial_listLength

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts
open scoped BigOperators Classical
noncomputable section

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)

lemma profileBoxViews_actual (x : PaperStates r c) :
    profileBoxViews (stateCodeData r c e x)=
      List.ofFn (fun k : ProfileIndex (m := m) (n := n) (q := q) =>
        splitViews (q,List.ofFn (fun i =>
          ((finFunctionFinEquiv.symm k : ProfileBox (m := m) (n := n) (q := q)) i).val))) := by
  have hlen : ((cellCatalog (paperSmall r c) e++cellCatalog (paperSmall r c) e).map
      (fun _ => false)).length=q+q := by
    simp only [List.length_map,List.length_append,cellCatalog,List.length_ofFn]
  unfold profileBoxViews profileEnumerationData stateCodeData codeCheckData
  rw [gridWords_finFunctions _ (d^20) (q+q) hlen,List.map_ofFn]
  simp only [cellCatalog,List.length_ofFn]
  rfl

lemma profileBoxViews_decoded (x : PaperStates r c) :
    (profileBoxViews (stateCodeData r c e x)).map (decodeStateCode r c e)=
      List.ofFn (profileAt r c e) := by
  rw [profileBoxViews_actual,List.map_ofFn]
  rfl

end
end ContingencyTables.SmallGraphProfiles

end OAI
