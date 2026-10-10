import OAI.NumberTheory.Jacobsthal.Primes.KloostermanPrimeBound

namespace OAI

namespace Erdos970

section

namespace ErdosKloosterman

theorem norm_le_three_quarters {F : Type*} [Field F] [Fintype F]
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (a b : F) (hab : a ≠ 0 ∨ b ≠ 0) :
    ‖sum ψ a b‖ ≤ 2 * (Fintype.card F : ℝ)^((3 : ℝ)/4) := by
  have hfour := fourth_norm_le ψ hψ a b hab
  have hq : 0 ≤ (Fintype.card F : ℝ) := Nat.cast_nonneg _
  have hp : ((Fintype.card F : ℝ)^((3 : ℝ)/4))^4 = (Fintype.card F : ℝ)^3 := by
    rw [← Real.rpow_mul_natCast hq]
    norm_num
  have hright : (2 * (Fintype.card F : ℝ)^((3 : ℝ)/4))^4 =
      16 * (Fintype.card F : ℝ)^3 := by rw [mul_pow, hp]; norm_num
  have hb : ‖sum ψ a b‖^4 ≤ (2 * (Fintype.card F : ℝ)^((3 : ℝ)/4))^4 := by
    rw [hright]
    nlinarith [show 0 ≤ (Fintype.card F : ℝ)^3 by positivity]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by decide : 4 ≠ 0)).mp hb

theorem standardSum_prime_bound (p : ℕ) [Fact p.Prime] (h k : ℤ)
    (hk : (h : ZMod p) ≠ 0 ∨ (k : ZMod p) ≠ 0) :
    ‖standardSum p h k‖ ≤ 2 * (p : ℝ)^((3 : ℝ)/4) := by
  simpa only [standardSum, ZMod.card] using
    norm_le_three_quarters ZMod.stdAddChar (ZMod.isPrimitive_stdAddChar p)
      (h : ZMod p) (k : ZMod p) hk

end ErdosKloosterman

end

end Erdos970

end OAI
