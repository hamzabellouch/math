import Mathlib
import OAI.Combinatorics.KMedianRecovery.Encoding.UniformBits

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySeed
open WordOperations BinaryArithmetic
lemma uniform_value (b : ℕ) (s : Fin b→Bool) :
    value (List.ofFn s).reverse=(Categorical.uniformBits b s).val := by
  induction b with
  | zero=>rfl
  | succ b ih=>
    rw [List.ofFn_succ,List.reverse_cons,value_append,List.length_reverse,List.length_ofFn,ih]
    simp only [value,Nat.mul_zero,Nat.add_zero]
    cases hs : s 0 <;> simp [Categorical.uniformBits,Equiv.trans_apply,Fin.consEquiv,finTwoEquiv,finProdFinEquiv,hs] <;> rfl
noncomputable def normalizeBig (x : List Bool) : List Bool := BinaryArithmetic.normalize x.reverse
noncomputable def normalizeBig_computes : PolyComputes normalizeBig := reverse_computes.comp BinaryDivision.normalize_computes
lemma normalizeBig_ofFn (b : ℕ) (s : Fin b→Bool) :
    normalizeBig (List.ofFn s)=(Categorical.uniformBits b s).val.bits := by rw [normalizeBig,normalize_eq_bits,uniform_value]
end MetricKMedianRecovery.BitMachine.BinarySeed

end OAI
