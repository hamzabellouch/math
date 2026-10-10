import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordCandidateExecution
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.SamplerVectorCells

namespace OAI

/-! # Counted rejection returning the successful sampler seed

The full candidate buffer is produced once from the word stream and tested
by the tail rejection loop. The accepted value supplies the unused
backup coordinate. Generation work, evaluator work and peak storage are
explicit; no execution cost is assigned to arbitrary program continuations.
-/

namespace LowSpaceSubsetSum.WordSeedRejectionExecution

open WordSeedRealization

variable {w k : ℕ}

theorem program_run_bind {α β : Type} (stream : ℕ → Fin (2^w))
    (p : WordProgram.Program w α) (next : α → WordProgram.Program w β) (cursor : ℕ) :
    WordProgram.run stream (WordProgram.bind p next) cursor =
      let r := WordProgram.run stream p cursor
      WordProgram.run stream (next r.1) r.2 := by
  induction p generalizing cursor with
  | pure a => rfl
  | draw branch ih =>
    simp only [WordProgram.bind,WordProgram.run]
    exact ih _ _

theorem program_run_map {α β : Type} (stream : ℕ → Fin (2^w))
    (p : WordProgram.Program w α) (f : α → β) (cursor : ℕ) :
    WordProgram.run stream (WordProgram.map f p) cursor =
      let r := WordProgram.run stream p cursor
      (f r.1,r.2) := by
  exact program_run_bind stream p (fun a => .pure (f a)) cursor

theorem tuple_run (stream : ℕ → Fin (2^w)) (N cursor : ℕ) :
    WordProgram.run stream (WordTuple.sample N) cursor =
      ((fun i : Fin N => stream (cursor+i.val)),cursor+N) := by
  induction N generalizing cursor with
  | zero =>
    apply Prod.ext
    · funext i
      exact Fin.elim0 i
    · rfl
  | succ N ih =>
    simp only [WordTuple.sample,WordProgram.run,program_run_map,ih]
    apply Prod.ext
    · funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero,Fin.val_zero,Nat.add_zero]
      · simp only [Fin.cons_succ,Fin.val_succ]
        congr 1
        omega
    · omega

variable (A : Fin (2^k) → Prop) [DecidablePred A]
  [Nonempty {a : Fin (2^k) // A a}]

def attach (N : ℕ) (f : Fin N → Fin (2^k)) (o : Option {a : Fin (2^k) // A a})
    (ho : o = firstAcceptSubtype A N f) :
    Option (SuccessfulSeed (firstAcceptCoupling A N)) :=
  match o with
  | none => none
  | some a => some ⟨(f,a),a,ho.symm⟩

theorem attach_eq (N : ℕ) (f : Fin N → Fin (2^k)) (o : Option {a : Fin (2^k) // A a})
    (ho : o = firstAcceptSubtype A N f) :
    attach A N f o ho = rejectionSeed A N f := by
  cases o with
  | none =>
    dsimp only [attach]
    unfold rejectionSeed
    split
    · rfl
    next a ha =>
      have h := ho.trans ha
      contradiction
  | some a =>
    dsimp only [attach]
    unfold rejectionSeed
    split
    next hnone =>
      have h := ho.trans hnone
      contradiction
    next b hb =>
      have h : a = b := Option.some.inj (ho.trans hb)
      subst b
      rfl

variable (evaluate : Fin (2^k) → (Bool × ℕ) × ℕ)
  (he : ∀ a, (evaluate a).1.1 = true ↔ A a)

theorem tested_value (N : ℕ) (v : Vector (Fin (2^k)) N) :
    (SamplerVectorCells.test A evaluate he 1 N v).1.value =
      firstAcceptSubtype A N (SamplerVectorCells.candidates v) := by
  let backup : {a : Fin (2^k) // A a} := Classical.choice inferInstance
  exact (congrArg SamplerExecution.Trace.value
    (SamplerVectorCells.test_value A evaluate he 1 N v backup)).trans
      ((SamplerExecution.test A (fun a => (evaluate a).1) he N).value_eq
        (SamplerVectorCells.candidates v,backup))

structure Trace (N : ℕ) where
  seed : Option (SuccessfulSeed (firstAcceptCoupling A N))
  cursor : ℕ
  testedCandidates : ℕ
  testWork : ℕ
  work : ℕ
  cells : ℕ

def run (stream : ℕ → Fin (2^w)) (modulus : ℕ) (hm : modulus = 2^k)
    (N cursor : ℕ) : Trace A N :=
  let words := WordCandidateExecution.run stream modulus hm N cursor
  let tested := SamplerVectorCells.test A evaluate he 1 N words.data
  ⟨attach A N (SamplerVectorCells.candidates words.data) tested.1.value
      (tested_value A evaluate he N words.data),
    words.cursor,tested.1.reads,tested.1.tests,
    words.work+6*tested.1.reads+tested.1.tests+8,
    max words.cells (N+tested.2+16)⟩

theorem run_seed (stream : ℕ → Fin (2^w)) (modulus : ℕ) (hm : modulus = 2^k)
    (N cursor : ℕ) :
    (run A evaluate he stream modulus hm N cursor).seed =
      rejectionSeed A N (fun i => ExactWordDraw.low w k (stream (cursor+i.val))) := by
  unfold run
  dsimp only
  rw [attach_eq,WordCandidateExecution.run_data]
  congr 1
  funext i
  simp only [SamplerVectorCells.candidates,Vector.getElem_ofFn]

theorem run_cursor (stream : ℕ → Fin (2^w)) (modulus : ℕ) (hm : modulus = 2^k)
    (N cursor : ℕ) : (run A evaluate he stream modulus hm N cursor).cursor = cursor+N :=
  WordCandidateExecution.run_cursor stream modulus hm N cursor

theorem program_value (hk : k ≤ w) (stream : ℕ → Fin (2^w))
    (modulus : ℕ) (hm : modulus = 2^k) (N cursor : ℕ) :
    ((run A evaluate he stream modulus hm N cursor).seed,
      (run A evaluate he stream modulus hm N cursor).cursor) =
      WordProgram.run stream (rejection w k hk N A).program cursor := by
  rw [run_seed,run_cursor]
  change _ = WordProgram.run stream
    (WordProgram.map (fun f => rejectionSeed A N
      (fun i => ExactWordDraw.low w k (f i))) (WordTuple.sample N)) cursor
  rw [program_run_map,tuple_run]

theorem tested_bounds (K N : ℕ) (hK : ∀ a, (evaluate a).1.2 ≤ K)
    (v : Vector (Fin (2^k)) N) :
    (SamplerVectorCells.test A evaluate he 1 N v).1.reads ≤ N ∧
      (SamplerVectorCells.test A evaluate he 1 N v).1.tests ≤ N*K := by
  let backup : {a : Fin (2^k) // A a} := Classical.choice inferInstance
  rw [SamplerVectorCells.test_value A evaluate he 1 N v backup]
  exact SamplerExecution.test_bounded A (fun a => (evaluate a).1) he N K hK
    (SamplerVectorCells.candidates v,backup)

theorem run_work (stream : ℕ → Fin (2^w)) (modulus : ℕ) (hm : modulus = 2^k)
    (K N cursor : ℕ) (hK : ∀ a, (evaluate a).1.2 ≤ K) :
    (run A evaluate he stream modulus hm N cursor).work ≤ N*(K+11)+9 := by
  have h := tested_bounds A evaluate he K N hK
    (WordCandidateExecution.run stream modulus hm N cursor).data
  change (WordCandidateExecution.run stream modulus hm N cursor).work+_+_+8 ≤ _
  rw [WordCandidateExecution.run_work]
  nlinarith only [h.1,h.2]

theorem run_cells (stream : ℕ → Fin (2^w)) (modulus : ℕ) (hm : modulus = 2^k)
    (H N cursor : ℕ) (hH : ∀ a, (evaluate a).2 ≤ H) :
    (run A evaluate he stream modulus hm N cursor).cells ≤ 2*N+H+56 := by
  have hw := WordCandidateExecution.run_cells stream modulus hm N cursor
  have ht := SamplerVectorCells.test_cells A evaluate he 1 H N
    (WordCandidateExecution.run stream modulus hm N cursor).data hH
  change max _ (N+_+16) ≤ _
  simp only [Nat.mul_one] at ht
  omega

end LowSpaceSubsetSum.WordSeedRejectionExecution

end OAI
