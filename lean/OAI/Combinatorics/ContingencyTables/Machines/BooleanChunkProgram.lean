import OAI.Combinatorics.ContingencyTables.Dense.DenseWordProgram

namespace OAI

/-! # Polynomial partition of a supplied Boolean word into fixed-width rows -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped Polynomial

def wordChunk (z : (ℕ×List Bool)×ℕ) : List Bool :=
  (z.1.2.drop (z.2*z.1.1)).take z.1.1

def wordChunkRealizer : Realizer wordChunk :=
  composition (pair
    (composition (pair (composition first second)
      (composition (pair second (composition first first)) multiply)) dropFast)
    (composition first first)) takeFast

theorem polynomial_wordChunk : PolynomialTime wordChunkRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second)
      (polynomial_composition (polynomial_pair polynomial_second
        (polynomial_composition polynomial_first polynomial_first)) polynomial_multiply))
      polynomial_dropFast)
    (polynomial_composition polynomial_first polynomial_first)) polynomial_takeFast

def completeWordRows (z : ℕ×List Bool) : List ℕ := List.range (z.2.length/z.1)

def completeWordRowsRealizer : Realizer completeWordRows :=
  composition (composition (pair (composition second listLength) first) quotient) range

theorem polynomial_completeWordRows : PolynomialTime completeWordRowsRealizer := by
  apply polynomial_boundedRange
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_second polynomial_listLength) polynomial_first)
      polynomial_quotient) X
  intro z
  simp only [eval_X,Function.comp_apply]
  exact (Nat.div_le_self _ _).trans ((list_length_le_weight _).trans (weight_snd z))

def wordChunks (z : ℕ×List Bool) : List (List Bool) :=
  (completeWordRows z).map (fun i => wordChunk (z,i))

def wordChunksRealizer : Realizer wordChunks :=
  composition (pair identity completeWordRowsRealizer) (mapWith wordChunkRealizer)

theorem polynomial_wordChunks : PolynomialTime wordChunksRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_completeWordRows)
    (polynomial_mapWith polynomial_wordChunk)

lemma wordChunk_ofFn {n k : ℕ} (bits : Fin (n*k) → Bool) (i : Fin n) :
    wordChunk ((k,List.ofFn bits),i.val)=
      List.ofFn (fun j : Fin k => bits (finProdFinEquiv (i,j))) := by
  have hbound : k ≤ n*k-i.val*k := by
    apply Nat.le_sub_of_add_le
    simpa only [Nat.succ_mul,Nat.add_comm] using
      Nat.mul_le_mul_right k (Nat.succ_le_of_lt i.isLt)
  apply List.ext_getElem
  · simp only [wordChunk,List.length_take,List.length_drop,List.length_ofFn,min_eq_left hbound]
  · intro j _ _
    simp only [wordChunk,List.getElem_take,List.getElem_drop,List.getElem_ofFn]
    apply congrArg bits
    apply Fin.ext
    change i.val*k+j=j+k*i.val
    ac_rfl

theorem wordChunks_ofFn {n k : ℕ} (hk : 0<k) (bits : Fin (n*k) → Bool) :
    wordChunks (k,List.ofFn bits)=
      List.ofFn (fun i : Fin n => List.ofFn (fun j : Fin k => bits (finProdFinEquiv (i,j)))) := by
  have hrows : completeWordRows (k,List.ofFn bits)=List.range n := by
    simp only [completeWordRows,List.length_ofFn,Nat.mul_div_cancel _ hk]
  unfold wordChunks
  rw [hrows]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,List.length_ofFn]
  · intro i hi _
    have hin : i<n := by simpa only [List.length_map,List.length_range] using hi
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
    exact wordChunk_ofFn bits ⟨i,hin⟩

end ContingencyTables.DensePrograms

end OAI
