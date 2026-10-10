import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordTuple
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.SamplerAttempts

namespace OAI

/-! # A fair-word implementation of the measured bounded rejection loop

Only the polynomial-size candidate tuple is drawn and retained. The same
measured evaluator then supplies output, read count, and test-work count.
-/

namespace LowSpaceSubsetSum.WordRejection

open WordProgram

def run (w k N : ℕ) (evaluate : Fin (2^k) → Bool × ℕ) :
    Program w (Option (Fin (2^k)) × ℕ × ℕ) :=
  WordProgram.map (fun f => SamplerAttempts.runCostAcc evaluate N
    (fun i => ExactWordDraw.low w k (f i)) 0 0) (WordTuple.sample N)

theorem bounded (w k N : ℕ) (evaluate : Fin (2^k) → Bool × ℕ) :
    Bounded (run w k N evaluate) N := by
  simpa only [run, WordProgram.map, Nat.add_zero] using
    WordProgram.bind_bound (WordTuple.sample (w := w) N) N (WordTuple.bounded N)
      (fun f => .pure (SamplerAttempts.runCostAcc evaluate N
        (fun i => ExactWordDraw.low w k (f i)) 0 0)) 0 (fun _ => Bounded.pure _ 0)

theorem probability (w k : ℕ) (hk : k ≤ w) (N : ℕ)
    (A : Fin (2^k) → Prop) [DecidablePred A] [Nonempty {a : Fin (2^k) // A a}]
    (evaluate : Fin (2^k) → Bool × ℕ)
    (P : (Option (Fin (2^k)) × ℕ × ℕ) → Prop) :
    WordProgram.probability (run w k N evaluate) P =
      (firstAcceptCoupling A N).law.probability
        (fun s => P (SamplerAttempts.runCostAcc evaluate N s.1 0 0)) := by
  rw [run, WordProgram.probability_map, WordTuple.probability]
  exact (ExactWordDraw.candidates_words w k hk A N
    (fun f => P (SamplerAttempts.runCostAcc evaluate N f 0 0))).symm

def sample (w k N : ℕ) (A : Fin (2^k) → Prop) [DecidablePred A] :
    Program w (Option {a : Fin (2^k) // A a}) :=
  WordProgram.map (fun f => firstAcceptSubtype A N
    (fun i => ExactWordDraw.low w k (f i))) (WordTuple.sample N)

theorem sample_bounded (w k N : ℕ) (A : Fin (2^k) → Prop) [DecidablePred A] :
    Bounded (sample w k N A) N := by
  simpa only [sample, WordProgram.map, Nat.add_zero] using
    WordProgram.bind_bound (WordTuple.sample (w := w) N) N (WordTuple.bounded N)
      (fun f => .pure (firstAcceptSubtype A N (fun i => ExactWordDraw.low w k (f i)))) 0
      (fun _ => Bounded.pure _ 0)

theorem sample_probability (w k : ℕ) (hk : k ≤ w) (N : ℕ)
    (A : Fin (2^k) → Prop) [DecidablePred A] [Nonempty {a : Fin (2^k) // A a}]
    (P : Option {a : Fin (2^k) // A a} → Prop) :
    WordProgram.probability (sample w k N A) P =
      (firstAcceptCoupling A N).boundedLaw.probability P := by
  rw [sample, WordProgram.probability_map, WordTuple.probability,
    SamplerCoupling.boundedLaw, FiniteLaw.map_probability]
  exact (ExactWordDraw.firstAccept_words w k hk A N P).symm

theorem sample_expectation (w k : ℕ) (hk : k ≤ w) (N : ℕ)
    (A : Fin (2^k) → Prop) [DecidablePred A] [Nonempty {a : Fin (2^k) // A a}]
    (f : Option {a : Fin (2^k) // A a} → ℝ) :
    WordProgram.expectation (sample w k N A) f =
      (firstAcceptCoupling A N).boundedLaw.expectation f :=
  WordProgram.expectation_of_probability _ _ (sample_probability w k hk N A) f

end LowSpaceSubsetSum.WordRejection

end OAI
