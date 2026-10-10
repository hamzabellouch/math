import Mathlib
import OAI.Computability.MinUncut.Machines.Runtime
import OAI.Computability.MinUncut.Estimates.OutputSize

namespace OAI

section
namespace MinUncut
open Turing MinUncutGames.Foundations.Complexity
lemma Output.vertices_le_bits (G : Output) : G.vertices≤G.bits.length := by
  have h:G.vertices≤G.vertices^2:=by
    by_cases hz:G.vertices=0
    · simp [hz]
    · have hp:1≤G.vertices:=Nat.one_le_iff_ne_zero.mpr hz
      simpa only [pow_two,Nat.mul_one] using Nat.mul_le_mul_left G.vertices hp
  rw [G.bits_length]
  omega
lemma graph_size_of_runtime (M : FinTM2) (G : Output)
    (input : List (M.Γ M.k₀)) (out : List (M.Γ M.k₁)) (B : ℕ)
    (hlen : out.length=G.bits.length)
    (hr : TM2OutputsInTime M input (some out) B) :
    G.vertices+G.bits.length≤2*(input.length+B*Runtime.programPushBound M) := by
  have hb:=Runtime.outputLength_le M input out B hr
  rw [hlen] at hb
  calc
    _ ≤ G.bits.length+G.bits.length := Nat.add_le_add_right G.vertices_le_bits _
    _ = 2*G.bits.length := (two_mul _).symm
    _ ≤ _ := Nat.mul_le_mul_left 2 hb
end MinUncut

end

end OAI
