import Mathlib
import OAI.Combinatorics.KMedianRecovery.Encoding.WordExtras

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList.Take
open WordOperations BinaryArithmetic
noncomputable def number (x : List Bool) : List Bool :=
  (value (lengthBits (discardPrefix x))-value (extractPrefix x)).bits
noncomputable def number_computes : PolyComputes number :=
  NatOps.sub (discardPrefix_computes.comp lengthBits_computes) extractPrefix_computes
noncomputable def run (x : List Bool) : List Bool :=
  reverse (Drop.run (pairBits (number x,reverse (discardPrefix x))))
attribute [local irreducible] number reverse Drop.run
noncomputable def run_computes : PolyComputes run :=
  ((number_computes.pair (discardPrefix_computes.comp reverse_computes)).comp Drop.run_computes).comp reverse_computes
lemma run_encode (n : ℕ) (ws : List (List Bool)) :
    run (pairBits (n.bits,encode ws))=encode (ws.take n) := by
  simp only [run,number,extractPrefix_pairBits,discardPrefix_pairBits,lengthBits_encode,value_bits,
    reverse_encode,Drop.run_encode,List.reverse_drop,List.reverse_reverse,List.length_reverse]
  congr 1
  rw [show ws.length-(ws.length-n)=min n ws.length by omega]
  exact List.take_eq_take_min.symm
end MetricKMedianRecovery.BitMachine.WordList.Take

end OAI
