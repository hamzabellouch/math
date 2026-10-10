import OAI.Combinatorics.ContingencyTables.Machines.BooleanChunkProgram
import OAI.Combinatorics.ContingencyTables.Dense.DenseBooleanTrial

namespace OAI

/-! # Splitting a binary word at input-dependent coordinate widths -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped Polynomial

abbrev DependentChunkData := (List ℕ×List Bool)×ℕ

def chunkStart (z : DependentChunkData) : ℕ := (z.1.1.take z.2).sum
def chunkStartRealizer : Realizer chunkStart :=
  composition (composition (pair (composition first first) second) takeFast) listSum

theorem polynomial_chunkStart : PolynomialTime chunkStartRealizer :=
  polynomial_composition (polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_first) polynomial_second)
    polynomial_takeFast) polynomial_listSum

def dependentChunk (z : DependentChunkData) : List Bool :=
  (z.1.2.drop (chunkStart z)).take (z.1.1.getD z.2 0)

def dependentChunkRealizer : Realizer dependentChunk :=
  composition (pair
    (composition (pair (composition first second) chunkStartRealizer) dropFast)
    (composition (pair (composition first first) second) (getDFast 0))) takeFast

theorem polynomial_dependentChunk : PolynomialTime dependentChunkRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second) polynomial_chunkStart)
      polynomial_dropFast)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      (polynomial_getDFast 0))) polynomial_takeFast

def chunkIndices (z : List ℕ×List Bool) : List ℕ := List.range z.1.length
def chunkIndicesRealizer : Realizer chunkIndices := composition (composition first listLength) range

theorem polynomial_chunkIndices : PolynomialTime chunkIndicesRealizer := by
  apply polynomial_boundedRange (polynomial_composition polynomial_first polynomial_listLength) X
  intro z
  simpa only [Function.comp_apply,eval_X] using
    (list_length_le_weight z.1).trans (weight_fst z)

def dependentChunks (z : List ℕ×List Bool) : List (List Bool) :=
  (chunkIndices z).map (fun i => dependentChunk (z,i))
def dependentChunksRealizer : Realizer dependentChunks :=
  composition (pair identity chunkIndicesRealizer) (mapWith dependentChunkRealizer)

theorem polynomial_dependentChunks : PolynomialTime dependentChunksRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_chunkIndices)
    (polynomial_mapWith polynomial_dependentChunk)

open scoped BigOperators

lemma take_ofFn_sum {q : ℕ} (width : Fin q → ℕ) (i : Fin q) :
    ((List.ofFn width).take i.val).sum=∑ j : Fin i.val,width (Fin.castLE i.isLt.le j) := by
  rw [←Fin.ofFn_take_eq_take_ofFn i.isLt.le,List.sum_ofFn]
  rfl

theorem dependentChunk_ofFn {q : ℕ} (width : Fin q → ℕ)
    (bits : Fin (∑ i,width i) → Bool) (i : Fin q) :
    dependentChunk ((List.ofFn width,List.ofFn bits),i.val)=
      List.ofFn (fun j : Fin (width i) => bits (finSigmaFinEquiv ⟨i,j⟩)) := by
  have hw : (List.ofFn width).getD i.val 0=width i := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,i.isLt,dite_true,Option.getD_some,Fin.eta]
  have hb : ((List.ofFn width).take i.val).sum+width i≤∑ j,width j := by
    by_cases hi : width i=0
    · rw [hi,Nat.add_zero,←List.sum_ofFn]
      exact (List.take_sublist i.val (List.ofFn width)).sum_le_sum (fun _ _ => Nat.zero_le _)
    · have hh := (finSigmaFinEquiv (⟨i,⟨width i-1,by omega⟩⟩ : Sigma (fun i => Fin (width i)))).isLt
      rw [finSigmaFinEquiv_apply,←take_ofFn_sum] at hh
      dsimp only at hh
      omega
  have hlen : width i≤(∑ j,width j)-((List.ofFn width).take i.val).sum :=
    Nat.le_sub_of_add_le (by omega)
  apply List.ext_getElem
  · simp only [dependentChunk,chunkStart,List.length_take,List.length_drop,List.length_ofFn,hw,
      min_eq_left hlen]
  · intro j hj _
    simp only [dependentChunk,chunkStart,List.getElem_take,List.getElem_drop,List.getElem_ofFn]
    apply congrArg bits
    apply Fin.ext
    simp only [finSigmaFinEquiv_apply,take_ofFn_sum]

theorem dependentChunks_ofFn {q : ℕ} (width : Fin q → ℕ)
    (bits : Fin (∑ i,width i) → Bool) :
    dependentChunks (List.ofFn width,List.ofFn bits)=
      List.ofFn (fun i => List.ofFn (fun j : Fin (width i) => bits (finSigmaFinEquiv ⟨i,j⟩))) := by
  unfold dependentChunks chunkIndices
  rw [List.length_ofFn]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,List.length_ofFn]
  · intro i hi _
    have hiq : i < q := by simpa only [List.length_map,List.length_range] using hi
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
    exact dependentChunk_ofFn width bits ⟨i,hiq⟩

end ContingencyTables.DensePrograms

end OAI
