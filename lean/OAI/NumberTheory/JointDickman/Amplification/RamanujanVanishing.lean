import OAI.NumberTheory.JointDickman.Amplification.RamanujanMultiplicative
import Mathlib.Data.Nat.Factorization.Basic

namespace OAI

/-! # Vanishing of the Ramanujan factor at a missing repeated prime -/

namespace JointDickman
open scoped ArithmeticFunction.Moebius

theorem ramanujanSum_coprime {q : ℕ} [NeZero q] {k : ℕ}
    (hk : k.Coprime q) : ramanujanSum q (k : ZMod q) = (μ q : ℂ) := by
  simpa only [ZMod.coe_unitOfCoprime] using
    ramanujanSum_unit (ZMod.unitOfCoprime k hk)

theorem ramanujanSum_prime_power_zero {p a k : ℕ} [NeZero (p^a)] (hp : p.Prime)
    (ha : 2 ≤ a) (hk : ¬p ∣ k) :
    ramanujanSum (p^a) (k : ZMod (p^a)) = 0 := by
  rw [ramanujanSum_coprime ((hp.coprime_iff_not_dvd.mpr hk).symm.pow_right a),
    ArithmeticFunction.moebius_apply_prime_pow hp (by omega), ite_eq_right (by omega)]
  simp

theorem ramanujanSum_zero_of_prime_sq_dvd {n p k : ℕ} [NeZero n]
    (hp : p.Prime) (hpn : p^2 ∣ n) (hpk : ¬p ∣ k) :
    ramanujanSum n (k : ZMod n) = 0 := by
  let a := n.factorization p
  let b := n / p^a
  have ha : 2 ≤ a := (hp.pow_dvd_iff_le_factorization (NeZero.ne n)).mp hpn
  have hdiv : p^a ∣ n := Nat.ordProj_dvd n p
  have he : p^a*b = n := Nat.mul_div_cancel' hdiv
  have hb : b ≠ 0 := by
    intro hb
    have : n = 0 := by rw [← he, hb, mul_zero]
    exact NeZero.ne n this
  let : NeZero (p^a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let : NeZero b := ⟨hb⟩
  have hcop : (p^a).Coprime b := (Nat.coprime_ordCompl hp (NeZero.ne n)).pow_left a
  rw [ramanujanSum_eq_arithmetic, ← he,
    (ramanujanArithmetic_multiplicative k).map_mul_of_coprime hcop,
    ← ramanujanSum_eq_arithmetic, ramanujanSum_prime_power_zero hp ha hpk, zero_mul]

theorem ramanujanSum_zero_of_not_coprime {j q k : ℕ} [NeZero (j*q)]
    (hjq : ¬j.Coprime q) (hk : k.Coprime q) :
    ramanujanSum (j*q) (k : ZMod (j*q)) = 0 := by
  obtain ⟨p,hp,hpj,hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp hjq
  apply ramanujanSum_zero_of_prime_sq_dvd hp
  · simpa only [pow_two] using Nat.mul_dvd_mul hpj hpq
  · intro hpk
    exact hp.ne_one (Nat.eq_one_of_dvd_coprimes hk hpk hpq)

end JointDickman

end OAI
