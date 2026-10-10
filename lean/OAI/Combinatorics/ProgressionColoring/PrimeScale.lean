import OAI.Combinatorics.ProgressionColoring.Parameters
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic.FieldSimp

namespace OAI

noncomputable section

namespace QuantitativeVanDerWaerden.Parameters

/-- A positive power of an integer base lies within one base factor of any
real target at least one. -/
theorem exists_power_near {P : ℕ} (hP : 2 ≤ P) {x : ℝ} (hx : 1 ≤ x) :
    ∃ n : ℕ, 0 < n ∧ x ≤ ((P ^ n : ℕ) : ℝ) ∧
      ((P ^ n : ℕ) : ℝ) ≤ (P : ℝ) * x := by
  have hP1 : (1 : ℝ) < P := by exact_mod_cast hP
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near hx hP1
  refine ⟨n + 1, Nat.succ_pos _, ?_, ?_⟩
  · simpa only [Nat.cast_pow] using hn'.le
  · calc
      ((P ^ (n + 1) : ℕ) : ℝ) = (P : ℝ) ^ n * P := by
        rw [Nat.cast_pow, pow_succ]
      _ ≤ x * (P : ℝ) := mul_le_mul_of_nonneg_right hn (Nat.cast_nonneg P)
      _ = (P : ℝ) * x := mul_comm _ _

/-- The elementary prime bound used in the cyclic construction. -/
theorem exists_prime_above {k : ℕ} (hk : 2 ≤ k) :
    ∃ P : ℕ, P.Prime ∧ k < P ∧ P ≤ 2 * k ^ 2 := by
  obtain ⟨P, hP, hkP, hPk⟩ :=
    Nat.exists_prime_lt_and_le_two_mul k (by omega)
  refine ⟨P, hP, hkP, hPk.trans ?_⟩
  nlinarith

/-- The complete arithmetic choice of prime and prime-power base. -/
structure PrimeScale (k D : ℕ) where
  P : ℕ
  exponent : ℕ
  q : ℕ
  prime : P.Prime
  prime_lower : k < P
  prime_upper : P ≤ 2 * k ^ 2
  exponent_pos : 0 < exponent
  q_eq_pow : q = P ^ exponent
  q_lower : (k : ℝ) ^ (c * k / D) ≤ (q : ℝ)
  q_upper : (q : ℝ) ≤ 2 * (k : ℝ) ^ 2 * (k : ℝ) ^ (c * k / D)

theorem exists_primeScale {k D : ℕ} (hk : 2 ≤ k) (hD : 1 ≤ D) :
    Nonempty (PrimeScale k D) := by
  obtain ⟨P, hP, hkP, hPk⟩ := exists_prime_above hk
  have hc := c_pos
  have hx : 1 ≤ (k : ℝ) ^ (c * k / D) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ k by omega)) (by positivity)
  obtain ⟨n, hn, hlow, hupp⟩ := exists_power_near hP.two_le hx
  refine ⟨{
    P := P
    exponent := n
    q := P ^ n
    prime := hP
    prime_lower := hkP
    prime_upper := hPk
    exponent_pos := hn
    q_eq_pow := rfl
    q_lower := hlow
    q_upper := hupp.trans ?_
  }⟩
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast hPk
  · exact Real.rpow_nonneg (Nat.cast_nonneg k) _

namespace PrimeScale

variable {k D : ℕ} (s : PrimeScale k D)

theorem isPrimePow : IsPrimePow s.q := by
  rw [s.q_eq_pow]
  exact s.prime.isPrimePow.pow (Nat.ne_of_gt s.exponent_pos)

theorem two_le : 2 ≤ s.q := s.isPrimePow.two_le

theorem pos : 0 < s.q := s.isPrimePow.pos

theorem log_lower (hk : 2 ≤ k) (hD : 1 ≤ D) :
    c * k * Real.log k ≤ (D : ℝ) * Real.log s.q := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have hl := Real.log_le_log (Real.rpow_pos_of_pos hk0 _) s.q_lower
  rw [Real.log_rpow hk0] at hl
  have h := mul_le_mul_of_nonneg_left hl hD0.le
  calc
    c * k * Real.log k = (D : ℝ) * ((c * k / D) * Real.log k) := by
      field_simp [hD0.ne']
    _ ≤ (D : ℝ) * Real.log s.q := h

theorem log_upper (hk : 2 ≤ k) (hD : 1 ≤ D) :
    (D : ℝ) * Real.log s.q ≤
      c * k * Real.log k + (D : ℝ) * Real.log (2 * (k : ℝ) ^ 2) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have hq0 : (0 : ℝ) < s.q := by exact_mod_cast s.pos
  have ht0 := Real.rpow_pos_of_pos hk0 (c * k / D)
  have hf0 : (0 : ℝ) < 2 * (k : ℝ) ^ 2 := by positivity
  have hl := Real.log_le_log hq0 s.q_upper
  rw [Real.log_mul hf0.ne' ht0.ne', Real.log_rpow hk0] at hl
  calc
    (D : ℝ) * Real.log s.q ≤
        (D : ℝ) * (Real.log (2 * (k : ℝ) ^ 2) + (c * k / D) * Real.log k) :=
      mul_le_mul_of_nonneg_left hl hD0.le
    _ = c * k * Real.log k + (D : ℝ) * Real.log (2 * (k : ℝ) ^ 2) := by
      field_simp [hD0.ne']
      ring

/-- The cardinality of the cyclic group has the required superexponential scale. -/
theorem cardinal_lower (hk : 2 ≤ k) (hD : 1 ≤ D) :
    (k : ℝ) ^ (c * k) ≤ ((s.q ^ D : ℕ) : ℝ) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have he : (c * (k : ℝ) / D) * D = c * k :=
    div_mul_cancel₀ _ hD0.ne'
  calc
    (k : ℝ) ^ (c * k) = ((k : ℝ) ^ (c * k / D)) ^ D := by
      rw [← Real.rpow_mul_natCast hk0.le, he]
    _ ≤ (s.q : ℝ) ^ D :=
      pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg k) _) s.q_lower D
    _ = ((s.q ^ D : ℕ) : ℝ) := by rw [Nat.cast_pow]

end PrimeScale

end QuantitativeVanDerWaerden.Parameters

end

end OAI
