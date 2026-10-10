import OAI.Combinatorics.EditApproximation.Coarse.CoarseChildrenBitWork

namespace OAI

namespace EditApproximation
namespace BinaryFraction

/-- Loose magnitude bound for all partial child sums. Its bit length is
linear in the depth and parameter bit lengths. -/
def coarseLevelMagnitude (N k B d : ℕ) : ℕ :=
  (N + k + 1) * (2 * B + 2) ^ (d + 1)

 theorem coarseLevelMagnitude_pos (N k B d : ℕ) : 0 < coarseLevelMagnitude N k B d := by
  unfold coarseLevelMagnitude
  positivity

 theorem coarseLevelMagnitude_ge (N k B d : ℕ) : k ≤ coarseLevelMagnitude N k B d := by
  have hp : 1 ≤ (2 * B + 2) ^ (d + 1) := by
    have hz : 0 < (2 * B + 2) ^ (d + 1) := by positivity
    omega
  unfold coarseLevelMagnitude
  nlinarith

 theorem coarseLevelMagnitude_mono (N k B d e : ℕ) (h : d ≤ e) :
    coarseLevelMagnitude N k B d ≤ coarseLevelMagnitude N k B e := by
  unfold coarseLevelMagnitude
  apply Nat.mul_le_mul_left
  exact Nat.pow_le_pow_right (by omega) (by omega)

 theorem coarseLevelMagnitude_succ (N k B d : ℕ) :
    B * (coarseLevelMagnitude N k B d + k) + 2 ≤ coarseLevelMagnitude N k B (d + 1) := by
  have hk := coarseLevelMagnitude_ge N k B d
  have hp := coarseLevelMagnitude_pos N k B d
  have heq : coarseLevelMagnitude N k B (d + 1) =
      coarseLevelMagnitude N k B d * (2 * B + 2) := by
    unfold coarseLevelMagnitude
    rw [show d + 1 + 1 = (d + 1) + 1 by omega, pow_succ]
    ring
  rw [heq]
  nlinarith

 theorem coarseLevelMagnitude_bits (N k B d : ℕ) :
    Nat.size (coarseLevelMagnitude N k B d) ≤
      Nat.size (N + k + 1) + (d + 1) * Nat.size (2 * B + 2) + 1 := by
  have hm := natural_product_bit_length (N + k + 1) ((2 * B + 2) ^ (d + 1))
  have hp := natural_power_bit_length (2 * B + 2) (d + 1)
  unfold coarseLevelMagnitude
  omega

end BinaryFraction
end EditApproximation

end OAI
