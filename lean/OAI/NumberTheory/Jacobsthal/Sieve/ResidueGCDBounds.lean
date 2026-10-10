import OAI.NumberTheory.Jacobsthal.Estimates.UnitCyclicBounds

namespace OAI

namespace Erdos970

section

namespace ErdosHyperbolaError

theorem gcd_three_le_second (N x y : ℕ) (hN : 0 < N) :
    Nat.gcd N (Nat.gcd x y) ≤ Nat.gcd y N := by
  apply Nat.le_of_dvd (Nat.gcd_pos_of_pos_right y hN)
  exact Nat.dvd_gcd ((Nat.gcd_dvd_right N (Nat.gcd x y)).trans (Nat.gcd_dvd_right x y))
    (Nat.gcd_dvd_left N (Nat.gcd x y))

theorem gcd_natCast_val (N : ℕ) [NeZero N] (x : ℕ) :
    Nat.gcd ((x : ZMod N).val) N = Nat.gcd x N := by
  rw [ZMod.val_natCast, ← Nat.gcd_rec, Nat.gcd_comm N]

theorem gcd_shift_le (H T x j : ℕ) (hH : 0 < H) (hT : 0 < T) :
    Nat.gcd (x+H*j) (H*T) ≤ T * Nat.gcd x (H*T) := by
  let g := Nat.gcd (x+H*j) (H*T)
  have hgx : g ∣ x+H*j := Nat.gcd_dvd_left _ _
  have hgN : g ∣ H*T := Nat.gcd_dvd_right _ _
  have hsum : g ∣ T*(x+H*j) := dvd_mul_of_dvd_right hgx T
  have hNj : g ∣ (H*T)*j := dvd_mul_of_dvd_left hgN j
  have he : T*(x+H*j) = T*x+(H*T)*j := by ring
  rw [he] at hsum
  have hTx : g ∣ T*x := (Nat.dvd_add_iff_left hNj).mpr hsum
  have hTN : g ∣ T*(H*T) := dvd_mul_of_dvd_right hgN T
  have hd : g ∣ T*Nat.gcd x (H*T) := by
    simpa only [Nat.gcd_mul_left] using Nat.dvd_gcd hTx hTN
  exact Nat.le_of_dvd (mul_pos hT (Nat.gcd_pos_of_pos_right x (mul_pos hH hT))) hd

theorem shifted_gcd_le (H T : ℕ) [NeZero H] [NeZero T]
    (h : ZMod (H*T)) (j : ZMod T) :
    Nat.gcd (h+(H : ZMod (H*T))*(j.val : ZMod (H*T))).val (H*T) ≤
      T*Nat.gcd h.val (H*T) := by
  have he : h+(H : ZMod (H*T))*(j.val : ZMod (H*T)) =
      ((h.val+H*j.val : ℕ) : ZMod (H*T)) := by simp
  rw [he, gcd_natCast_val]
  exact gcd_shift_le H T h.val j.val (NeZero.pos H) (NeZero.pos T)

end ErdosHyperbolaError

end

end Erdos970

end OAI
