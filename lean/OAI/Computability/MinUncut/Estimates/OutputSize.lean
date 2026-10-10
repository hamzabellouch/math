import Mathlib
import OAI.Computability.MinUncut.Machines.MachineBinaryFormula

namespace OAI

section
noncomputable section
namespace MinUncut
open MinUncutGames.BinaryEncoding

lemma bitName_length_le (n : ℕ) : (nameBits n).length≤2*n+1 := by
  rw [nameBits_length]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.size_le.mpr n.lt_two_pow_self)) _

lemma Output.bits_length (G : Output) :
    G.bits.length=(nameBits G.vertices).length+G.vertices^2+(nameBits G.threshold).length := by
  unfold Output.bits
  simp only [List.length_append,List.length_flatMap,List.length_map,List.length_finRange]
  simp [pow_two]

lemma Output.bits_length_le (G : Output) :
    G.bits.length≤2*G.vertices+1+G.vertices^2+(2*G.threshold+1) := by
  rw [G.bits_length]
  exact add_le_add (Nat.add_le_add_right (bitName_length_le _) _) (bitName_length_le _)
end MinUncut

end
end

end OAI
