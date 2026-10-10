import Mathlib
import OAI.Combinatorics.KMedian.Binary.BinaryListExtras
import OAI.Combinatorics.KMedian.Binary.BinaryIterations

namespace OAI


                                          
section
namespace MetricKMedian.Binary
open Function Polynomial PolyProgram
namespace Dyadic

def twice (q : ℚ) : ℚ := q*2
def powers (n : ℕ) : List ℚ := Iteration.iterates twice 1 (n.size+1)
theorem iterate_twice (i : ℕ) : twice^[i] 1=(2:ℚ)^i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply',ih]; exact (pow_succ ..).symm
theorem powers_eq (n : ℕ) : powers n=(List.range (n.size+1)).map (fun t => (2:ℚ)^t) := by
  simp only [powers,Iteration.iterates_eq,iterate_twice]
theorem height_pow (i : ℕ) : HasHeight ((2:ℚ)^i) i := by
  induction i with
  | zero => simpa using HasHeight.one 0
  | succ i ih =>
      rw [pow_succ]
      exact ih.mul (by norm_num [HasHeight])
noncomputable def program : PolyProgram Nat.bits (encodeList Ratio.encode) powers := by
  let P : PolyProgram Ratio.encode Ratio.encode twice :=
    (((identity Ratio.encode).fanout (constant Ratio.encode Ratio.encode 2)).comp ratMul).congr _ (fun _ => rfl)
  let N := (natSize.fanout (constant Nat.bits Nat.bits 1)).comp natAdd
  exact (P.iteratesFrom (constant Nat.bits Ratio.encode 1) N 0 (X+1) (3*(X+1)+10)
    (fun n => by simp only [eval_add,eval_X,eval_one,Nat.size_eq_bits_len,Function.comp_apply,le_refl])
    (fun n i hi => by
      rw [iterate_twice]
      have hb := Ratio.length_height (height_pow i)
      simp only [eval_add,eval_mul,eval_ofNat,eval_X,eval_one,Nat.size_eq_bits_len]
      dsimp only [Function.comp_apply] at hi
      omega)).congr _ (fun _ => rfl)
end Dyadic
end MetricKMedian.Binary
end

end OAI
