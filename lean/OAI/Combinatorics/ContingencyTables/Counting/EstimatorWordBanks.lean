import OAI.Combinatorics.ContingencyTables.Machines.BooleanChunkProgram
import OAI.Combinatorics.ContingencyTables.Dense.DenseMetropolisSemantics

namespace OAI

/-! # The exact disjoint word layout of one weight estimator

There is one bank of ratio samples for every phase, followed by one bank
of correction samples. Each correction sample has its own walk and bin
words. This is the literal layout used by the executable allocator.
-/

namespace ContingencyTables.EstimatorWordBanks

open DensePrograms GridBoundary FairBits
open scoped Classical

abbrev Banks (j S r t b : ℕ) :=
  (Fin j → Fin S → Fin r → Bool) ×
    (Fin S → (Fin t → Bool) × (Fin b → Bool))

def wordEquiv (j S r t b : ℕ) :
    (Fin (j*(S*r)+S*(t+b)) → Bool) ≃ Banks j S r t b :=
  (splitWordEquiv _ _).trans (Equiv.prodCongr
    ((gridWordEquiv j (S*r)).trans
      (Equiv.piCongrRight (fun _ => gridWordEquiv S r)))
    ((gridWordEquiv S (t+b)).trans
      (Equiv.piCongrRight (fun _ => splitWordEquiv t b))))

lemma ratio_chunks (j S r t b : ℕ) (hr : 0 < r)
    (bits : Fin (j*(S*r)+S*(t+b)) → Bool) (a : Fin j) :
    wordChunks (r,wordChunk ((S*r,(List.ofFn bits).take (j*(S*r))),a.val))=
      List.ofFn (fun i : Fin S => List.ofFn ((wordEquiv j S r t b bits).1 a i)) := by
  rw [ofFn_split_take,wordChunk_ofFn]
  rw [wordChunks_ofFn hr]
  rfl

lemma ratio_rows (j S r t b : ℕ) (hs : 0 < S) (hr : 0 < r)
    (bits : Fin (j*(S*r)+S*(t+b)) → Bool) :
    completeWordRows (S*r,(List.ofFn bits).take (j*(S*r)))=List.range j := by
  rw [ofFn_split_take]
  simp only [completeWordRows,List.length_ofFn,Nat.mul_div_cancel _ (Nat.mul_pos hs hr)]

lemma correction_chunks (j S r t b : ℕ) (ht : 0 < t+b)
    (bits : Fin (j*(S*r)+S*(t+b)) → Bool) :
    (wordChunks (t+b,(List.ofFn bits).drop (j*(S*r)))).take S=
      List.ofFn (fun i : Fin S => List.ofFn
        (gridWordEquiv S (t+b) (splitWordEquiv (j*(S*r)) (S*(t+b)) bits).2 i)) := by
  rw [ofFn_split_drop,wordChunks_ofFn ht]
  exact List.take_of_length_le (by simp)

lemma correction_take (j S r t b : ℕ)
    (bits : Fin (j*(S*r)+S*(t+b)) → Bool) (i : Fin S) :
    (List.ofFn (gridWordEquiv S (t+b)
      (splitWordEquiv (j*(S*r)) (S*(t+b)) bits).2 i)).take t=
        List.ofFn ((wordEquiv j S r t b bits).2 i).1 := by
  rw [ofFn_split_take]
  rfl

lemma correction_drop (j S r t b : ℕ)
    (bits : Fin (j*(S*r)+S*(t+b)) → Bool) (i : Fin S) :
    (List.ofFn (gridWordEquiv S (t+b)
      (splitWordEquiv (j*(S*r)) (S*(t+b)) bits).2 i)).drop t=
        List.ofFn ((wordEquiv j S r t b bits).2 i).2 := by
  rw [ofFn_split_drop]
  rfl

end ContingencyTables.EstimatorWordBanks

end OAI
