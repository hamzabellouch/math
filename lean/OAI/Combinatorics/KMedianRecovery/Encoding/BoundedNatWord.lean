import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.RawSlices
import OAI.Combinatorics.KMedianRecovery.Recovery.RawUnary

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BoundedNatWord
open WordOperations
noncomputable def counter (P : Polynomial ℕ) : PolynomialCounter P := PolynomialCounter.choose P
noncomputable def run (P : Polynomial ℕ) (x : List Bool) : List Bool :=
  RawUnary.run (RawTake.run (pairBits (extractPrefix x,(counter P).word (discardPrefix x))))
attribute [local irreducible] RawTake.run RawUnary.run counter
noncomputable def run_computes (P : Polynomial ℕ) : PolyComputes (run P) :=
  ((extractPrefix_computes.pair (discardPrefix_computes.comp (counter P).computes)).comp
    RawTake.run_computes).comp RawUnary.run_computes
lemma run_pack (P : Polynomial ℕ) (n : ℕ) (w : List Bool) :
    run P (pairBits (n.bits,w))=List.replicate (min n (P.eval w.length)) true := by
  simp only [run,extractPrefix_pairBits,discardPrefix_pairBits,RawTake.run_pack,RawUnary.run,
    List.length_take,(counter P).word_length]
lemma run_exact (P : Polynomial ℕ) (n : ℕ) (w : List Bool) (hn : n≤P.eval w.length) :
    run P (pairBits (n.bits,w))=List.replicate n true := by
  rw [run_pack,min_eq_left hn]
end MetricKMedianRecovery.BitMachine.BoundedNatWord

end OAI
