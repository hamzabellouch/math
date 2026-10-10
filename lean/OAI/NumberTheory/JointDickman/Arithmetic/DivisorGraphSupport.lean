import OAI.NumberTheory.JointDickman.Counting.OffDiagonalEnergy
import OAI.NumberTheory.JointDickman.Amplification.ArithGraph

namespace OAI

/-! # Arithmetic support of the unequal-coefficient graph edges -/

namespace JointDickman
open Finset

theorem coprime_of_divisor_linear_succ {a c m : ℕ} (h : c ∣ a*m+1) :
    a.Coprime c ∧ m.Coprime c := by
  have ha : a.Coprime (a*m+1) :=
    (Nat.coprime_mul_left_add_right a 1 m).mpr (Nat.coprime_one_right a)
  have hm : m.Coprime (a*m+1) :=
    (Nat.coprime_mul_right_add_right m 1 a).mpr (Nat.coprime_one_right m)
  exact ⟨ha.coprime_dvd_right h, hm.coprime_dvd_right h⟩

theorem amplificationInnerWeight_support {T a c : ℕ}
    (h : amplificationInnerWeight T a c ≠ 0) :
    T*c < a ∧ a < 2*(T*c) := by
  have hs := amplificationBump_support h
  have hd : T*c ≠ 0 := by
    intro he
    have hz : (T : ℝ)*(c : ℝ) = 0 := by exact_mod_cast he
    simp only [amplificationInnerWeight, hz, div_zero] at h
    exact h (amplificationBump_zero (Or.inl (by norm_num)))
  have hp : (0 : ℝ) < (T : ℝ)*c := by exact_mod_cast Nat.pos_of_ne_zero hd
  constructor
  · have hl : (T : ℝ)*c < a := by simpa only [one_mul] using (lt_div_iff₀ hp).mp hs.1
    exact_mod_cast hl
  · exact_mod_cast (div_lt_iff₀ hp).mp hs.2

/-- Both congruences and the coefficient window force a small nonzero lag. -/
theorem divisor_pair_small_lag {T a b c m : ℕ}
    (ha : c ∣ a*m+1) (hb : c ∣ b*m+1) (hab : a ≠ b)
    (hwa : T*c < a ∧ a < 2*(T*c)) (hwb : T*c < b ∧ b < 2*(T*c)) :
    ∃ j : ℤ, j ≠ 0 ∧ (a : ℤ)-b = j*c ∧ j.natAbs < T := by
  have hc : 0 < c := by nlinarith [hwa.1, hwa.2]
  have hdiv : (c : ℤ) ∣ (a : ℤ)-b := common_divisor_difference (m := (m : ℤ))
    (by exact_mod_cast ha) (by exact_mod_cast hb)
  obtain ⟨j,hj⟩ := hdiv
  have he : (a : ℤ)-b = j*c := by simpa only [mul_comm] using hj
  have hj0 : j ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul, sub_eq_zero] at he
    exact hab (by exact_mod_cast he)
  have hbnd : |(a : ℤ)-b| < (T : ℤ)*c := by
    apply abs_lt.mpr
    constructor <;> omega
  rw [he, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ c)] at hbnd
  have hjs : |j| < (T : ℤ) := (mul_lt_mul_iff_left₀ (by exact_mod_cast hc : (0 : ℤ) < c)).mp
    (by simpa only [mul_comm] using hbnd)
  refine ⟨j,hj0,he,?_⟩
  rw [← Int.natCast_natAbs] at hjs
  exact_mod_cast hjs

/-- A prime-product coefficient is coprime to every nonzero small lag. -/
theorem auxiliaryProduct_coprime_small {B : ℕ} {A : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) {d : ℕ} (hd : 0 < d)
    (hdsmall : d ≤ auxiliaryCutoff B) : (∏ p ∈ A, p).Coprime d := by
  apply Nat.coprime_of_dvd
  intro p hp hpa hpd
  have hpos : (∏ p ∈ A, p) ≠ 0 := prod_ne_zero_iff.mpr
    (fun q hq => (auxiliaryPrimes_prime B q (hA hq)).ne_zero)
  have hpA := hp.mem_primeFactors hpa hpos
  rw [Nat.primeFactors_prod (fun q hq => auxiliaryPrimes_prime B q (hA hq))] at hpA
  have hpP := hA hpA
  have hpgt : auxiliaryCutoff B < p := by
    exact_mod_cast (mem_filter.mp hpP).2
  exact (not_lt_of_ge ((Nat.le_of_dvd hd hpd).trans hdsmall)) hpgt

/-- Once the coefficient is coprime to the lag and to c, the edge's two
coefficients are coprime. This is the cancellation used by the inverse map. -/
theorem divisor_edge_coprime {a b c : ℕ} {j : ℤ}
    (hac : a.Coprime c) (haj : a.Coprime j.natAbs)
    (he : (a : ℤ)-b = j*c) : a.Coprime b := by
  apply Nat.coprime_of_dvd'
  intro p hp hpa hpb
  have hpjc : (p : ℤ) ∣ j*c := by
    rw [← he]
    exact dvd_sub (by exact_mod_cast hpa) (by exact_mod_cast hpb)
  have hpjc' : p ∣ j.natAbs*c := by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using Int.natCast_dvd.mp hpjc
  have hpj : p ∣ j.natAbs := (hac.coprime_dvd_left hpa).dvd_mul_right.mp hpjc'
  exact Nat.dvd_one.mpr (Nat.eq_one_of_dvd_coprimes haj hpa hpj)

end JointDickman

end OAI
