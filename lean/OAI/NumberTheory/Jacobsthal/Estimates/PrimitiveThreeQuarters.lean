import OAI.NumberTheory.Jacobsthal.Primes.TwoPrimeRoots

namespace OAI

namespace Erdos970

section

namespace ErdosKloosterman.PrimePower

theorem quadraticUnitRoots_card_le_four_prime_power (p s : ℕ) [Fact p.Prime]
    (hs : 0 < s) (a b : ZMod (p^s)) (ha : IsUnit a) :
    (quadraticUnitRoots (p^s) a b).card ≤ 4 := by
  by_cases hp2 : p = 2
  · subst p
    exact quadraticUnitRoots_card_le_four s hs a b ha
  · exact (quadraticUnitRoots_card_le_two p s hs hp2 a b ha).trans (by decide)

theorem int_frequency_isUnit (p s : ℕ) [Fact p.Prime] (hs : 0 < s) (h : ℤ)
    (hh : (h : ZMod p) ≠ 0) : IsUnit (h : ZMod (p^s)) := by
  apply (isUnit_iff_primeReduction_ne_zero p s hs _).mpr
  simpa only [map_intCast] using hh

theorem primitive_half_bound (p r s : ℕ) [Fact p.Prime] (hs : 0 < s) (hsr : s ≤ r)
    (h k : ℤ) (hhk : (h : ZMod p) ≠ 0 ∨ (k : ZMod p) ≠ 0) :
    ‖standardSum (p^(r+s)) h k‖ ≤ 4 * (p^r : ℕ) := by
  have left (h k : ℤ) (hh : (h : ZMod p) ≠ 0) :
      ‖standardSum (p^(r+s)) h k‖ ≤ 4 * (p^r : ℕ) := by
    have hn := standard_norm_le_stationary_card p r s hsr h k
    have hc := stationary_card_le_root_card_mul (p^r) (p^s)
      (h : ZMod (p^r*p^s)) (k : ZMod (p^r*p^s))
    have hr : (quadraticUnitRoots (p^s)
        (reduction (p^r) (p^s) (h : ZMod (p^r*p^s)))
        (reduction (p^r) (p^s) (k : ZMod (p^r*p^s)))).card ≤ 4 := by
      simpa only [map_intCast] using quadraticUnitRoots_card_le_four_prime_power p s hs
        (h : ZMod (p^s)) (k : ZMod (p^s)) (int_frequency_isUnit p s hs h hh)
    have hc4 := hc.trans (Nat.mul_le_mul_right (p^r) hr)
    have hc4real : ((stationaryUnits ((p^r : ℕ) : ZMod (p^r*p^s))
        (h : ZMod (p^r*p^s)) k).card : ℝ) ≤ 4 * (p^r : ℕ) := by
      exact_mod_cast hc4
    have transport (N : ℕ) [NeZero N] (hN : N = p^r*p^s) :
        ((stationaryUnits ((p^r : ℕ) : ZMod N) (h : ZMod N) k).card : ℝ) ≤
          4 * (p^r : ℕ) := by
      subst N
      exact hc4real
    exact hn.trans (transport (p^(r+s)) (pow_add p r s))
  rcases hhk with hh | hk
  · exact left h k hh
  · have he : standardSum (p^(r+s)) h k = standardSum (p^(r+s)) k h :=
      sum_swap ZMod.stdAddChar (h : ZMod (p^(r+s))) (k : ZMod (p^(r+s)))
    rw [he]
    exact left k h hk

end ErdosKloosterman.PrimePower

end

section

namespace ErdosKloosterman.PrimePower

theorem standardSum_modulus_congr (N M : ℕ) [NeZero N] [NeZero M]
    (hNM : N = M) (h k : ℤ) : standardSum N h k = standardSum M h k := by
  subst M
  rfl

theorem ceiling_half_le_three_quarters (p a : ℕ) (hp : 1 ≤ p) (ha : 2 ≤ a) :
    ((p^(a-a/2) : ℕ) : ℝ) ≤ ((p^a : ℕ) : ℝ)^((3 : ℝ)/4) := by
  have hexp : (a-a/2)*4 ≤ a*3 := by omega
  have hnat : (p^(a-a/2))^4 ≤ (p^a)^3 := by
    rw [← pow_mul, ← pow_mul]
    exact Nat.pow_le_pow_right hp hexp
  have hreal : (((p^(a-a/2) : ℕ) : ℝ))^4 ≤ (((p^a : ℕ) : ℝ))^3 := by
    exact_mod_cast hnat
  have he : ((((p^a : ℕ) : ℝ))^((3 : ℝ)/4))^4 = (((p^a : ℕ) : ℝ))^3 := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _)]
    norm_num
  rw [← he] at hreal
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide : 4 ≠ 0)).mp hreal

theorem primitive_three_quarter_bound (p a : ℕ) [Fact p.Prime] (ha : 2 ≤ a)
    (h k : ℤ) (hhk : (h : ZMod p) ≠ 0 ∨ (k : ZMod p) ≠ 0) :
    ‖standardSum (p^a) h k‖ ≤ 4 * ((p^a : ℕ) : ℝ)^((3 : ℝ)/4) := by
  have hs : 0 < a/2 := by omega
  have hsr : a/2 ≤ a-a/2 := by omega
  have he : a-a/2+a/2 = a := by omega
  have hhalf := primitive_half_bound p (a-a/2) (a/2) hs hsr h k hhk
  rw [standardSum_modulus_congr _ (p^a) (congrArg (p^·) he)] at hhalf
  exact hhalf.trans (mul_le_mul_of_nonneg_left
    (ceiling_half_le_three_quarters p a (Fact.out : p.Prime).one_le ha) (by positivity))

end ErdosKloosterman.PrimePower

end

end Erdos970

end OAI
