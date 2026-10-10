import OAI.Combinatorics.ProgressionColoring.PrimeScale
import OAI.Combinatorics.ProgressionColoring.Dilation
import OAI.Combinatorics.ProgressionColoring.CyclicModel
import OAI.Combinatorics.ProgressionColoring.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds

namespace OAI

namespace QuantitativeVanDerWaerden.ConstructionModel

open Parameters

abbrev Data (k : ℕ) := PrimeScale k (dimension k)

/-- Choose the arithmetic data whose existence is proved by the prime and
prime-power scale construction. No coloring or covering data is assumed. -/
noncomputable def choose (k : ℕ) (hk : 3 ≤ k) : Data k :=
  Classical.choice (exists_primeScale (by omega : 2 ≤ k)
    (show 1 ≤ dimension k from dimension_pos (by omega)))

noncomputable def lambda (k : ℕ) : ℕ := dilation ((dimension k) ^ 2) (cutoff k)

noncomputable def groupSize {k : ℕ} (s : Data k) : ℕ := s.q ^ dimension k

abbrev Group {k : ℕ} (s : Data k) := CyclicGroup s.q (dimension k)

theorem lambda_pos (k : ℕ) : 0 < lambda k := dilation_pos _ _

theorem lambda_ne_zero (k : ℕ) : lambda k ≠ 0 := (lambda_pos k).ne'

theorem groupSize_pos {k : ℕ} (s : Data k) : 0 < groupSize s :=
  pow_pos s.pos _

theorem groupSize_ne_zero {k : ℕ} (s : Data k) : groupSize s ≠ 0 :=
  (groupSize_pos s).ne'

/-- Available as a local instance without requiring typeclass inference
to reconstruct the prime-scale record from a projected modulus. -/
theorem groupSize_neZero {k : ℕ} (s : Data k) : NeZero (groupSize s) :=
  ⟨groupSize_ne_zero s⟩

@[instance_reducible] noncomputable def groupFintype {k : ℕ} (s : Data k) : Fintype (Group s) := by
  letI : NeZero (s.q ^ dimension k) := groupSize_neZero s
  exact inferInstance

theorem group_card {k : ℕ} (s : Data k) [Fintype (Group s)] :
    Fintype.card (Group s) = groupSize s := ZMod.card _

theorem groupSize_two_le {k : ℕ} (s : Data k) (hk : 3 ≤ k) :
    2 ≤ groupSize s := by
  exact s.two_le.trans (le_self_pow₀ (by have := s.two_le; omega)
    (dimension_pos (by omega : 1 ≤ k)).ne')

theorem groupSize_eq_prime_pow {k : ℕ} (s : Data k) :
    groupSize s = s.P ^ (s.exponent * dimension k) := by
  simp only [groupSize, s.q_eq_pow, pow_mul]

theorem groupSize_lower {k : ℕ} (s : Data k) (hk : 3 ≤ k) :
    (k : ℝ) ^ (c * k) ≤ (groupSize s : ℝ) :=
  s.cardinal_lower (by omega) (dimension_pos (by omega))

theorem prime_step {k : ℕ} (s : Data k) : k ≤ s.P := s.prime_lower.le

/-- The stronger basic-scale inequalities place every prime in the
dilation strictly below the prime defining the cyclic group. -/
theorem dimension_sq_lt_length {k : ℕ} (h : BasicScales k) :
    (dimension k) ^ 2 < k := by
  have hreal : (dimension k : ℝ) ^ 2 < (k : ℝ) := by
    have hgap := h.short_period_gap
    have hcut := h.cutoff_small
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  exact_mod_cast hreal

theorem lambda_coprime_of_dimension_sq_lt {k : ℕ} (s : Data k)
    (hD : (dimension k) ^ 2 < k) : Nat.Coprime (lambda k) (groupSize s) := by
  rw [groupSize_eq_prime_pow s]
  exact dilation_coprime_prime_pow s.prime (hD.trans s.prime_lower)

theorem lambda_coprime {k : ℕ} (s : Data k) (h : BasicScales k) :
    Nat.Coprime (lambda k) (groupSize s) :=
  lambda_coprime_of_dimension_sq_lt s (dimension_sq_lt_length h)

theorem affine_box_small {k : ℕ} (hk : 3 ≤ k) :
    2 * (k : ℝ) * meshScale k < 1 := by
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  unfold meshScale
  rw [mul_one_div]
  apply (div_lt_iff₀ (sq_pos_of_pos hk0)).2
  nlinarith

theorem one_le_log_length {k : ℕ} (hk : 3 ≤ k) :
    1 ≤ Real.log (k : ℝ) := by
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  apply (Real.le_log_iff_exp_le (by linarith : (0 : ℝ) < k)).2
  exact Real.exp_one_lt_d9.le.trans ((by norm_num : (2.7182818286 : ℝ) ≤ 3).trans hkR)

end QuantitativeVanDerWaerden.ConstructionModel

end OAI
