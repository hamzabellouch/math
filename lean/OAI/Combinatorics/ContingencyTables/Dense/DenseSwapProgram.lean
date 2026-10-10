import OAI.Combinatorics.ContingencyTables.Machines.MaximalListProgram
import OAI.Combinatorics.ContingencyTables.Dense.DenseDrawSemantics

namespace OAI

/-! # Binary row and column permutations for dense input normalization -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped Polynomial

def swapZeroIndex (z : ℕ×ℕ) : ℕ := if z.2=0 then z.1 else if z.2=z.1 then 0 else z.2

def swapZeroIndexRealizer : Realizer swapZeroIndex :=
  (choose (composition (pair second (constant 0)) natEqual) first
    (choose (composition (pair second first) natEqual) (constant 0) second)).congr
      (by intro z; simp only [swapZeroIndex,Function.comp_apply,decide_eq_true_eq])

theorem polynomial_swapZeroIndex : PolynomialTime swapZeroIndexRealizer :=
  polynomial_congr _ (polynomial_choose
    (polynomial_composition (polynomial_pair polynomial_second (polynomial_constant 0)) polynomial_natEqual)
    polynomial_first (polynomial_choose
      (polynomial_composition (polynomial_pair polynomial_second polynomial_first) polynomial_natEqual)
      (polynomial_constant 0) polynomial_second))

variable {A : Type} [Codec A] [Inhabited A]

def swapZeroEntry (z : (ℕ×List A)×ℕ) : A :=
  z.1.2.getD (swapZeroIndex (z.1.1,z.2)) default

def swapZeroEntryRealizer : Realizer (swapZeroEntry (A := A)) :=
  composition (pair (composition first second)
    (composition (pair (composition first first) second) swapZeroIndexRealizer)) (getDFast default)

theorem polynomial_swapZeroEntry : PolynomialTime (swapZeroEntryRealizer (A := A)) :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
    (polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_first)
      polynomial_second) polynomial_swapZeroIndex)) (polynomial_getDFast default)

def swapZeroIndices (z : ℕ×List A) : List ℕ := List.range z.2.length
def swapZeroIndicesRealizer : Realizer (swapZeroIndices (A := A)) :=
  composition (composition second listLength) range

omit [Inhabited A] in
theorem polynomial_swapZeroIndices : PolynomialTime (swapZeroIndicesRealizer (A := A)) := by
  apply polynomial_boundedRange (polynomial_composition polynomial_second polynomial_listLength) X
  intro z
  simpa only [Function.comp_apply,eval_X] using (list_length_le_weight z.2).trans (weight_snd z)

def swapZeroList (z : ℕ×List A) : List A :=
  (swapZeroIndices z).map (fun i => swapZeroEntry (z,i))

def swapZeroListRealizer : Realizer (swapZeroList (A := A)) :=
  composition (pair identity swapZeroIndicesRealizer) (mapWith swapZeroEntryRealizer)

theorem polynomial_swapZeroList : PolynomialTime (swapZeroListRealizer (A := A)) :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_swapZeroIndices)
    (polynomial_mapWith polynomial_swapZeroEntry)

def swapMatrixColumns (z : ℕ×MatrixCode) : MatrixCode :=
  z.2.map (fun row => swapZeroList (z.1,row))

def swapMatrixColumnsRealizer : Realizer swapMatrixColumns := mapWith swapZeroListRealizer

theorem polynomial_swapMatrixColumns : PolynomialTime swapMatrixColumnsRealizer :=
  polynomial_mapWith polynomial_swapZeroList

def swapMatrix (z : (ℕ×ℕ)×MatrixCode) : MatrixCode :=
  swapMatrixColumns (z.1.2,swapZeroList (z.1.1,z.2))

def swapMatrixRealizer : Realizer swapMatrix :=
  composition (pair (composition first second)
    (composition (pair (composition first first) second) swapZeroListRealizer)) swapMatrixColumnsRealizer

theorem polynomial_swapMatrix : PolynomialTime swapMatrixRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
    (polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_first)
      polynomial_second) polynomial_swapZeroList)) polynomial_swapMatrixColumns

open scoped Classical

lemma swapZeroIndex_val {n : ℕ} (p i : Fin (n+1)) :
    swapZeroIndex (p.val,i.val)=(Equiv.swap 0 p i).val := by
  by_cases hi : i=0
  · subst i
    rw [Equiv.swap_apply_left]
    simp only [swapZeroIndex,Fin.val_zero,ite_true]
  · have hi0 : i.val≠0 := fun h => hi (Fin.ext h)
    by_cases hp : i=p
    · subst i
      rw [Equiv.swap_apply_right]
      simp only [swapZeroIndex,hi0,ite_false,ite_true,Fin.val_zero]
    · have hip : i.val≠p.val := fun h => hp (Fin.ext h)
      rw [Equiv.swap_apply_of_ne_of_ne hi hp]
      simp only [swapZeroIndex,hi0,hip,ite_false]

omit [Codec A] in
theorem swapZeroList_ofFn {n : ℕ} (p : Fin (n+1)) (f : Fin (n+1) → A) :
    swapZeroList (p.val,List.ofFn f)=List.ofFn (fun i => f (Equiv.swap 0 p i)) := by
  apply List.ext_getElem
  · simp only [swapZeroList,swapZeroIndices,List.length_map,List.length_range,List.length_ofFn]
  · intro i hi _
    have hin : i < n+1 := by
      simpa only [swapZeroList,swapZeroIndices,List.length_map,List.length_range,List.length_ofFn] using hi
    simp only [swapZeroList,swapZeroIndices,List.getElem_map,List.getElem_range,List.getElem_ofFn,
      swapZeroEntry]
    rw [swapZeroIndex_val p ⟨i,hin⟩]
    rw [List.getD_eq_getElem (List.ofFn f) default (by simpa only [List.length_ofFn] using (Equiv.swap 0 p ⟨i,hin⟩).isLt)]
    simp only [List.getElem_ofFn,Fin.eta]

theorem swapMatrix_code {m n : ℕ} (i : Fin (m+1)) (j : Fin (n+1))
    (X : Fin (m+1) → Fin (n+1) → ℕ) :
    swapMatrix ((i.val,j.val),matrixCode X)=
      matrixCode (fun a b => X (Equiv.swap 0 i a) (Equiv.swap 0 j b)) := by
  unfold swapMatrix matrixCode
  rw [swapZeroList_ofFn]
  unfold swapMatrixColumns
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext a
  exact swapZeroList_ofFn j _

end ContingencyTables.DensePrograms

end OAI
