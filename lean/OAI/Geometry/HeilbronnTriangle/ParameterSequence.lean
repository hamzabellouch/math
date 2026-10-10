import OAI.Geometry.HeilbronnTriangle.PrimeParameters
import OAI.Geometry.HeilbronnTriangle.Parameters

namespace OAI


noncomputable section

namespace Problem355.Parameters

structure PrimeParameterData (k r : ℕ) where
  two_le_k : 2 ≤ k
  large_r : 200 * k ^ 2 ≤ r
  large_for_moment : 400 * k ^ 2 ≤ r
  B : ℕ
  q : ℕ
  base_prime : B.Prime
  auxiliary_prime : q.Prime
  base_lower : 100 * k ^ 2 * r ^ 30 < B
  base_upper : B ≤ 200 * k ^ 2 * r ^ 30
  base_polynomial : B ≤ r ^ 31
  auxiliary_lower : (B ^ k) ^ 100 < q
  auxiliary_upper : q ≤ 2 * (B ^ k) ^ 100
  auxiliary_polynomial : q ≤ (B ^ k) ^ 101
  coprime : (B ^ k).Coprime q
  auxiliary_large : 2000 * ((B ^ k) ^ 2) ^ 2 ≤ q

lemma exists_primeParameterData {k r : ℕ} (hk : 2 ≤ k)
    (hr : 400 * k ^ 2 ≤ r) : Nonempty (PrimeParameterData k r) := by
  have hr' : 200 * k ^ 2 ≤ r := by nlinarith only [hr]
  obtain ⟨B, q, hB, hq, hlo, hhi, hpoly, hqlo, hqhi, hqpoly, hcop, hlarge⟩ :=
    PrimeParameters.exists_prime_parameters k r (by omega) hr'
  exact ⟨⟨hk, hr', hr, B, q, hB, hq, hlo, hhi, hpoly, hqlo, hqhi, hqpoly, hcop, hlarge⟩⟩

namespace PrimeParameterData

variable {k r : ℕ} (P : PrimeParameterData k r)

def h : ℕ := P.B ^ k
def M : ℕ := P.h * P.q
def N : ℕ := P.M ^ 10
def tau : ℕ := threshold P.B k

include P in
lemma r_pos : 0 < r := by
  have hk := P.two_le_k
  have hp : 0 < 200 * k ^ 2 := by positivity
  exact lt_of_lt_of_le hp P.large_r

lemma base_ge_three : 3 ≤ P.B := by
  have hk : 0 < k := by have := P.two_le_k; omega
  have hr := P.r_pos
  have hp : 1 ≤ k ^ 2 * r ^ 30 := Nat.succ_le_of_lt (by positivity)
  have hc : 100 ≤ 100 * k ^ 2 * r ^ 30 := by
    calc
      100 = 100 * 1 := by norm_num
      _ ≤ 100 * (k ^ 2 * r ^ 30) := Nat.mul_le_mul_left 100 hp
      _ = 100 * k ^ 2 * r ^ 30 := by ring
  have := P.base_lower
  omega

lemma base_le_h : P.B ≤ P.h := by
  unfold h
  simpa using (Nat.pow_le_pow_right P.base_prime.pos (show 1 ≤ k by have := P.two_le_k; omega))

lemma h_ge_three : 3 ≤ P.h := P.base_ge_three.trans P.base_le_h

lemma h_le_M : P.h ≤ P.M := by
  unfold M
  exact Nat.le_mul_of_pos_right _ P.auxiliary_prime.pos

lemma r_le_M : r ≤ P.M := by
  have hr := P.r_pos
  have hk : 0 < k := by have := P.two_le_k; omega
  have hc : 1 ≤ 100 * k ^ 2 := Nat.succ_le_of_lt (by positivity)
  have hpow : r ≤ r ^ 30 := by
    simpa using Nat.pow_le_pow_right hr (by norm_num : 1 ≤ 30)
  calc
    r ≤ r ^ 30 := hpow
    _ ≤ 100 * k ^ 2 * r ^ 30 := Nat.le_mul_of_pos_left _ hc
    _ ≤ P.B := P.base_lower.le
    _ ≤ P.h := P.base_le_h
    _ ≤ P.M := P.h_le_M

lemma M_pos : 0 < P.M := lt_of_lt_of_le P.r_pos P.r_le_M

lemma M_le_N : P.M ≤ P.N := by
  unfold N
  simpa using Nat.pow_le_pow_right P.M_pos (by norm_num : 1 ≤ 10)

lemma N_pos : 0 < P.N := lt_of_lt_of_le P.M_pos P.M_le_N

lemma tau_pos : 0 < P.tau := threshold_pos P.base_ge_three P.two_le_k

lemma twice_tau_lt_h : 2 * P.tau < P.h :=
  twice_threshold_lt_power P.base_ge_three P.two_le_k

lemma tau_lt_h : P.tau < P.h := by
  have h := P.twice_tau_lt_h
  omega

lemma tau_le_cube : P.tau ≤ P.N ^ 3 := by
  calc
    P.tau ≤ P.h := P.tau_lt_h.le
    _ ≤ P.M := P.h_le_M
    _ ≤ P.N := P.M_le_N
    _ ≤ P.N ^ 3 := by
      simpa using Nat.pow_le_pow_right P.N_pos (by norm_num : 1 ≤ 3)

lemma box_polynomial : P.N ≤ r ^ (31620 * k) :=
  box_polynomial_bound P.base_polynomial P.auxiliary_polynomial

lemma ratio_polynomial : (P.h : ℝ) / (P.tau : ℝ) ≤ 3 * (r : ℝ) ^ 31 := by
  have hb : (P.B : ℝ) ≤ (r : ℝ) ^ 31 := by exact_mod_cast P.base_polynomial
  calc
    (P.h : ℝ) / (P.tau : ℝ) ≤ 3 * (P.B : ℝ) := ratio_bound P.base_ge_three P.two_le_k
    _ ≤ 3 * (r : ℝ) ^ 31 := mul_le_mul_of_nonneg_left hb (by norm_num)

lemma ratio_degree_thirty :
    (P.h : ℝ) / (P.tau : ℝ) ≤ 600 * (k : ℝ) ^ 2 * (r : ℝ) ^ 30 := by
  have hb : (P.B : ℝ) ≤ 200 * (k : ℝ) ^ 2 * (r : ℝ) ^ 30 := by
    exact_mod_cast P.base_upper
  calc
    (P.h : ℝ) / (P.tau : ℝ) ≤ 3 * (P.B : ℝ) := ratio_bound P.base_ge_three P.two_le_k
    _ ≤ 3 * (200 * (k : ℝ) ^ 2 * (r : ℝ) ^ 30) :=
      mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = 600 * (k : ℝ) ^ 2 * (r : ℝ) ^ 30 := by ring

lemma modulus_degree_thirty :
    (P.h : ℝ) ≤ (600 * (k : ℝ) ^ 2) * (P.tau : ℝ) * (r : ℝ) ^ 30 := by
  have ht : (0 : ℝ) < (P.tau : ℝ) := by exact_mod_cast P.tau_pos
  have hh := (div_le_iff₀ ht).mp P.ratio_degree_thirty
  calc
    (P.h : ℝ) ≤ (600 * (k : ℝ) ^ 2 * (r : ℝ) ^ 30) * (P.tau : ℝ) := hh
    _ = (600 * (k : ℝ) ^ 2) * (P.tau : ℝ) * (r : ℝ) ^ 30 := by ring

lemma base_lower_original : 100 * k ^ 2 * (r ^ 10) ^ 3 < P.B := by
  convert P.base_lower using 1; ring

lemma tau_lt_q : P.tau < P.q := by
  calc
    P.tau < P.h := P.tau_lt_h
    _ ≤ P.h ^ 100 := by
      simpa using Nat.pow_le_pow_right (by have := P.h_ge_three; omega : 0 < P.h)
        (by norm_num : 1 ≤ 100)
    _ < P.q := P.auxiliary_lower

lemma alphabet_lt_base : r ^ 10 < P.B := by
  have hk : 0 < k := by have := P.two_le_k; omega
  have hc : 1 ≤ 100 * k ^ 2 := Nat.succ_le_of_lt (by positivity)
  calc
    r ^ 10 ≤ r ^ 30 := Nat.pow_le_pow_right P.r_pos (by norm_num)
    _ ≤ 100 * k ^ 2 * r ^ 30 := Nat.le_mul_of_pos_left _ hc
    _ < P.B := P.base_lower

lemma digit_moment_bound :
    (P.B : ℝ) * ((r : ℝ) / (r : ℝ) ^ 10) ^ 4 ≤ 1 / 2 :=
  PrimeParameters.digit_moment_parameter_le_half k r P.B
    (by have := P.two_le_k; omega) P.large_for_moment P.base_upper

lemma real_bounds :
    (1 : ℝ) ≤ (P.N : ℝ) ∧ (1 : ℝ) ≤ (P.tau : ℝ) ∧
      (P.tau : ℝ) ≤ (P.N : ℝ) ^ 3 ∧ (r : ℝ) ≤ (P.M : ℝ) ∧
      (P.N : ℝ) ≤ (r : ℝ) ^ (31620 * k) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast P.N_pos
  · exact_mod_cast P.tau_pos
  · exact_mod_cast P.tau_le_cube
  · exact_mod_cast P.r_le_M
  · exact_mod_cast P.box_polynomial

end PrimeParameterData

lemma exists_parameter_sequence {k : ℕ} (hk : 2 ≤ k) :
    ∃ r : ℕ → ℕ, ∃ _P : (j : ℕ) → PrimeParameterData k (r j),
      Filter.Tendsto r Filter.atTop Filter.atTop ∧
      ∀ j, (r j).Prime ∧ Odd (r j) ∧ j ≤ r j := by
  classical
  obtain ⟨r0, hr0, hprime⟩ := PrimeParameters.exists_odd_prime_sequence
  let r : ℕ → ℕ := fun j => r0 (j + 400 * k ^ 2)
  have hj (j : ℕ) : j ≤ r j := by
    exact (Nat.le_add_right j (400 * k ^ 2)).trans (hprime (j + 400 * k ^ 2)).2.2
  have hlarge (j : ℕ) : 400 * k ^ 2 ≤ r j := by
    exact (Nat.le_add_left (400 * k ^ 2) j).trans (hprime (j + 400 * k ^ 2)).2.2
  let P : (j : ℕ) → PrimeParameterData k (r j) :=
    fun j => Classical.choice (exists_primeParameterData hk (hlarge j))
  refine ⟨r, P, Filter.tendsto_atTop_mono hj Filter.tendsto_id, ?_⟩
  intro j
  exact ⟨(hprime (j + 400 * k ^ 2)).1, (hprime (j + 400 * k ^ 2)).2.1, hj j⟩

lemma exists_heilbronn_parameter_sequence :
    ∃ r : ℕ → ℕ, ∃ _P : (j : ℕ) → PrimeParameterData heilbronnK (r j),
      Filter.Tendsto r Filter.atTop Filter.atTop ∧
      ∀ j, (r j).Prime ∧ Odd (r j) ∧ j ≤ r j :=
  exists_parameter_sequence (k := heilbronnK) heilbronnK_ge_two

end Problem355.Parameters

end

end OAI
