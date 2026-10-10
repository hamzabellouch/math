import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedExecution
import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedConstructors

namespace OAI

/-! # Materializing the actual words used by bounded rejection

The modulus is an already computed scalar argument. Each tail step reads
one word, reduces it modulo that scalar, and pushes the result into the
candidate array. The array is retained as part of the successful seed.
The counter charges five scalar operations per step and the final return;
the cell trace permits both the old and new array during a push.
-/

namespace LowSpaceSubsetSum.WordCandidateExecution

variable {w k : ℕ}

def low (modulus : ℕ) (hm : modulus = 2^k) (x : Fin (2^w)) : Fin (2^k) :=
  ⟨x.val % modulus, by rw [hm]; exact Nat.mod_lt _ (by positivity)⟩

theorem low_eq (modulus : ℕ) (hm : modulus = 2^k) (x : Fin (2^w)) :
    low modulus hm x = ExactWordDraw.low w k x := by
  subst modulus
  rfl

structure Raw (k : ℕ) where
  data : Array (Fin (2^k))
  cursor : ℕ
  work : ℕ
  cells : ℕ

def loop (stream : ℕ → Fin (2^w)) (modulus : ℕ) (hm : modulus = 2^k) :
    ℕ → ℕ → Array (Fin (2^k)) → ℕ → ℕ → Raw k
  | 0, cursor, acc, work, peak =>
      ⟨acc, cursor, work+1, max peak (2*acc.size+12)⟩
  | fuel+1, cursor, acc, work, peak =>
      let x := low modulus hm (stream cursor)
      loop stream modulus hm fuel (cursor+1) (acc.push x) (work+5)
        (max peak (2*(acc.size+1)+12))

theorem loop_data (stream : ℕ → Fin (2^w)) (modulus : ℕ) (hm : modulus = 2^k)
    (fuel cursor : ℕ) (acc : Array (Fin (2^k))) (work peak : ℕ) :
    (loop stream modulus hm fuel cursor acc work peak).data.toList =
      acc.toList ++ List.ofFn (fun i : Fin fuel => low modulus hm (stream (cursor+i.val))) := by
  induction fuel generalizing cursor acc work peak with
  | zero =>
    change acc.toList = acc.toList ++ List.ofFn (fun i : Fin 0 => _)
    simp only [List.ofFn_zero,List.append_nil]
  | succ fuel ih =>
    change (loop stream modulus hm fuel (cursor+1)
      (acc.push (low modulus hm (stream cursor))) (work+5)
        (max peak (2*(acc.size+1)+12))).data.toList = _
    rw [ih]
    simp only [Array.toList_push,List.ofFn_succ,Fin.val_zero,Nat.add_zero,
      Fin.val_succ,List.append_assoc,List.singleton_append]
    congr 2
    congr 1
    funext i
    congr 2
    omega

theorem loop_size (stream : ℕ → Fin (2^w)) (modulus : ℕ) (hm : modulus = 2^k)
    (fuel cursor : ℕ) (acc : Array (Fin (2^k))) (work peak : ℕ) :
    (loop stream modulus hm fuel cursor acc work peak).data.size = acc.size+fuel := by
  have h := congrArg List.length (loop_data stream modulus hm fuel cursor acc work peak)
  simpa only [Array.length_toList,List.length_append,List.length_ofFn] using h

theorem loop_cursor (stream : ℕ → Fin (2^w)) (modulus : ℕ) (hm : modulus = 2^k)
    (fuel cursor : ℕ) (acc : Array (Fin (2^k))) (work peak : ℕ) :
    (loop stream modulus hm fuel cursor acc work peak).cursor = cursor+fuel := by
  induction fuel generalizing cursor acc work peak with
  | zero => rfl
  | succ fuel ih =>
    change (loop stream modulus hm fuel (cursor+1)
      (acc.push (low modulus hm (stream cursor))) (work+5)
        (max peak (2*(acc.size+1)+12))).cursor = _
    rw [ih]
    omega

theorem loop_work (stream : ℕ → Fin (2^w)) (modulus : ℕ) (hm : modulus = 2^k)
    (fuel cursor : ℕ) (acc : Array (Fin (2^k))) (work peak : ℕ) :
    (loop stream modulus hm fuel cursor acc work peak).work = work+5*fuel+1 := by
  induction fuel generalizing cursor acc work peak with
  | zero =>
    change work+1 = work+5*0+1
    omega
  | succ fuel ih =>
    change (loop stream modulus hm fuel (cursor+1)
      (acc.push (low modulus hm (stream cursor))) (work+5)
        (max peak (2*(acc.size+1)+12))).work = _
    rw [ih]
    omega

theorem loop_cells (stream : ℕ → Fin (2^w)) (modulus : ℕ) (hm : modulus = 2^k)
    (fuel cursor : ℕ) (acc : Array (Fin (2^k))) (work peak : ℕ) :
    (loop stream modulus hm fuel cursor acc work peak).cells ≤
      max peak (2*(acc.size+fuel)+12) := by
  induction fuel generalizing cursor acc work peak with
  | zero =>
    change max peak (2*acc.size+12) ≤ max peak (2*(acc.size+0)+12)
    omega
  | succ fuel ih =>
    change (loop stream modulus hm fuel (cursor+1)
      (acc.push (low modulus hm (stream cursor))) (work+5)
        (max peak (2*(acc.size+1)+12))).cells ≤ _
    refine (ih _ _ _ _).trans ?_
    simp only [Array.size_push]
    omega

structure Buffer (k N : ℕ) where
  data : Vector (Fin (2^k)) N
  cursor : ℕ
  work : ℕ
  cells : ℕ

def run (stream : ℕ → Fin (2^w)) (modulus : ℕ) (hm : modulus = 2^k)
    (N cursor : ℕ) : Buffer k N :=
  let r := loop stream modulus hm N cursor #[] 0 0
  ⟨⟨r.data, by simpa only [Array.size_empty,Nat.zero_add] using
      loop_size stream modulus hm N cursor #[] 0 0⟩,
    r.cursor,r.work,r.cells⟩

theorem run_data (stream : ℕ → Fin (2^w)) (modulus : ℕ) (hm : modulus = 2^k)
    (N cursor : ℕ) :
    (run stream modulus hm N cursor).data = Vector.ofFn
      (fun i : Fin N => ExactWordDraw.low w k (stream (cursor+i.val))) := by
  apply Vector.toArray_inj.mp
  apply Array.toList_inj.mp
  simpa only [run,Array.toList_empty,List.nil_append,low_eq,
    Vector.toArray_ofFn,Array.toList_ofFn] using
      loop_data stream modulus hm N cursor #[] 0 0

theorem run_cursor (stream : ℕ → Fin (2^w)) (modulus : ℕ) (hm : modulus = 2^k)
    (N cursor : ℕ) : (run stream modulus hm N cursor).cursor = cursor+N :=
  loop_cursor stream modulus hm N cursor #[] 0 0

theorem run_work (stream : ℕ → Fin (2^w)) (modulus : ℕ) (hm : modulus = 2^k)
    (N cursor : ℕ) : (run stream modulus hm N cursor).work = 5*N+1 := by
  simpa only [run,Nat.zero_add] using loop_work stream modulus hm N cursor #[] 0 0

theorem run_cells (stream : ℕ → Fin (2^w)) (modulus : ℕ) (hm : modulus = 2^k)
    (N cursor : ℕ) : (run stream modulus hm N cursor).cells ≤ 2*N+12 := by
  simpa only [run,Array.size_empty,Nat.zero_add,Nat.zero_max] using
    loop_cells stream modulus hm N cursor #[] 0 0

end LowSpaceSubsetSum.WordCandidateExecution

end OAI
