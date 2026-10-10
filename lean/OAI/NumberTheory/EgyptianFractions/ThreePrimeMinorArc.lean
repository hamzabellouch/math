import OAI.NumberTheory.EgyptianFractions.BilinearFourier
import OAI.NumberTheory.EgyptianFractions.ThreePrimeMinorEnergy

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.ThreePrimeMinorArc

/-- The prime logarithmic polynomial has global size at most Chebyshev's
theta function, for arbitrary phases of norm at most one. -/
theorem prime_sum_norm_le_theta (u : ℕ) (phase : ℕ → ℂ)
    (hphase : ∀ p ∈ Nat.primesLE u, ‖phase p‖ ≤ 1) :
    ‖∑ p ∈ Nat.primesLE u, (Real.log (p : ℝ) : ℂ) * phase p‖ ≤
      Chebyshev.theta (u : ℝ) := by
  rw [Chebyshev.theta_eq_sum_primesLE_log]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  have hlog : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
  simpa using mul_le_mul_of_nonneg_left (hphase p hp) hlog

/-- An unconditional linear global amplitude bound, with an explicit constant. -/
theorem prime_sum_norm_le (u : ℕ) (phase : ℕ → ℂ)
    (hphase : ∀ p ∈ Nat.primesLE u, ‖phase p‖ ≤ 1) :
    ‖∑ p ∈ Nat.primesLE u, (Real.log (p : ℝ) : ℂ) * phase p‖ ≤
      Real.log 4 * (u : ℝ) :=
  (prime_sum_norm_le_theta u phase hphase).trans
    (Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg u))

/-- The cubic contribution of any set of frequencies is controlled by a
uniform bound on that set and the full Fourier energy. The twist may be any
function of norm at most one. This is the elementary minor-arc reduction,
not an assertion of a prime exponential-sum estimate. -/
theorem cubic_contribution_le_energy {q : ℕ} [NeZero q]
    (w : ZMod q → ℂ) (minor : Finset (ZMod q))
    (twist : ZMod q → ℂ) (A : ℝ) (hA : 0 ≤ A)
    (hbound : ∀ r ∈ minor, ‖residueFourier w r‖ ≤ A)
    (htwist : ∀ r ∈ minor, ‖twist r‖ ≤ 1) :
    ‖(∑ r ∈ minor, residueFourier w r ^ 3 * twist r) / (q : ℂ)‖ ≤
      A * ∑ n : ZMod q, ‖w n‖ ^ 2 := by
  have htransform (r : ZMod q) :
      residueFourier w r = ZMod.dft (fun n => w (-n)) r := by
    rw [ZMod.dft_comp_neg]
    simp only [residueFourier, ZMod.dft_apply, smul_eq_mul, mul_neg, neg_neg]
    apply Finset.sum_congr rfl
    intro n hn
    rw [mul_comm n r, mul_comm]
  have h := ThreePrimeMinorEnergy.minor_cubic_bound
    (fun n => w (-n)) twist minor A hA (by
      intro r hr
      rw [← htransform]
      exact hbound r hr) htwist
  simp_rw [← htransform] at h
  have henergy : (∑ n : ZMod q, ‖w (-n)‖ ^ 2) =
      ∑ n : ZMod q, ‖w n‖ ^ 2 :=
    Equiv.sum_comp (Equiv.neg _) (fun n => ‖w n‖ ^ 2)
  rw [henergy] at h
  simpa only [div_eq_mul_inv, mul_comm] using h

/-- The usual additive-character twist for the coefficient at `u`. -/
theorem cubic_character_contribution_le_energy {q : ℕ} [NeZero q]
    (w : ZMod q → ℂ) (minor : Finset (ZMod q)) (u : ZMod q)
    (A : ℝ) (hA : 0 ≤ A)
    (hbound : ∀ r ∈ minor, ‖residueFourier w r‖ ≤ A) :
    ‖(∑ r ∈ minor, residueFourier w r ^ 3 * ZMod.stdAddChar (-(r * u))) /
        (q : ℂ)‖ ≤ A * ∑ n : ZMod q, ‖w n‖ ^ 2 := by
  apply cubic_contribution_le_energy w minor _ A hA hbound
  intro r hr
  simp [ZMod.stdAddChar_apply]

/-- Prime logarithmic weights, zero padded in a cyclic group. -/
def primeLogWeight {q : ℕ} [NeZero q] (u : ℕ) (n : ZMod q) : ℂ :=
  if n.val ∈ Nat.primesLE u then (Real.log (n.val : ℝ) : ℂ) else 0

/-- Zero padding preserves the exact prime-weight energy when `u < q`. -/
theorem primeLogWeight_energy {q : ℕ} [NeZero q] (u : ℕ) (huq : u < q) :
    (∑ n : ZMod q, ‖primeLogWeight u n‖ ^ 2) =
      ∑ p ∈ Nat.primesLE u, Real.log (p : ℝ) ^ 2 := by
  classical
  calc
    (∑ n : ZMod q, ‖primeLogWeight u n‖ ^ 2) =
        ∑ n ∈ Finset.univ.filter (fun n : ZMod q => n.val ∈ Nat.primesLE u),
          Real.log (n.val : ℝ) ^ 2 := by
      simp [primeLogWeight, Finset.sum_filter, apply_ite, Complex.norm_real,
        Real.norm_eq_abs, sq_abs]
    _ = ∑ p ∈ Nat.primesLE u, Real.log (p : ℝ) ^ 2 := by
      apply Finset.sum_bij (fun n _ => n.val)
      · intro n hn
        exact (Finset.mem_filter.mp hn).2
      · intro n hn n' hn' heq
        exact ZMod.val_injective q heq
      · intro p hp
        have hpq : p < q := (Nat.mem_primesLE.mp hp).1.trans_lt huq
        refine ⟨(p : ZMod q), ?_, ZMod.val_natCast_of_lt hpq⟩
        simp [ZMod.val_natCast_of_lt hpq, hp]
      · intro n hn
        rfl

/-- The zero-padded transform is exactly the usual prime exponential sum. -/
theorem residueFourier_primeLogWeight {q : ℕ} [NeZero q]
    (u : ℕ) (huq : u < q) (r : ZMod q) :
    residueFourier (primeLogWeight u) r =
      ∑ p ∈ Nat.primesLE u,
        (Real.log (p : ℝ) : ℂ) * ZMod.stdAddChar (r * (p : ZMod q)) := by
  classical
  calc
    residueFourier (primeLogWeight u) r =
        ∑ n ∈ Finset.univ.filter (fun n : ZMod q => n.val ∈ Nat.primesLE u),
          (Real.log (n.val : ℝ) : ℂ) * ZMod.stdAddChar (r * n) := by
      simp [residueFourier, primeLogWeight, Finset.sum_filter, ite_mul]
    _ = ∑ p ∈ Nat.primesLE u,
        (Real.log (p : ℝ) : ℂ) * ZMod.stdAddChar (r * (p : ZMod q)) := by
      apply Finset.sum_bij (fun n _ => n.val)
      · intro n hn
        exact (Finset.mem_filter.mp hn).2
      · intro n hn n' hn' heq
        exact ZMod.val_injective q heq
      · intro p hp
        have hpq : p < q := (Nat.mem_primesLE.mp hp).1.trans_lt huq
        refine ⟨(p : ZMod q), ?_, ZMod.val_natCast_of_lt hpq⟩
        simp [ZMod.val_natCast_of_lt hpq, hp]
      · intro n hn
        simp only [ZMod.natCast_zmod_val]

/-- A Chebyshev energy bound saves one logarithm compared with the trivial
bound obtained by counting all integers up to `u`. -/
theorem prime_log_squares_le (u : ℕ) (hu : 1 ≤ u) :
    (∑ p ∈ Nat.primesLE u, Real.log (p : ℝ) ^ 2) ≤
      Real.log 4 * (u : ℝ) * Real.log (u : ℝ) := by
  have hlogu : 0 ≤ Real.log (u : ℝ) := Real.log_nonneg (by exact_mod_cast hu)
  calc
    (∑ p ∈ Nat.primesLE u, Real.log (p : ℝ) ^ 2) ≤
        ∑ p ∈ Nat.primesLE u, Real.log (p : ℝ) * Real.log (u : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hpu, hprime⟩ := Nat.mem_primesLE.mp hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
      have hplog : 0 ≤ Real.log (p : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hprime.one_le)
      have hlog : Real.log (p : ℝ) ≤ Real.log (u : ℝ) :=
        Real.log_le_log hp0 (by exact_mod_cast hpu)
      simpa [pow_two] using mul_le_mul_of_nonneg_left hlog hplog
    _ = Chebyshev.theta (u : ℝ) * Real.log (u : ℝ) := by
      rw [Chebyshev.theta_eq_sum_primesLE_log, Finset.sum_mul]
    _ ≤ Real.log 4 * (u : ℝ) * Real.log (u : ℝ) :=
      mul_le_mul_of_nonneg_right (Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg u)) hlogu

/-- A minor-frequency supremum bound for the actual prime sum yields a
quadratic error with the Chebyshev constant made explicit. -/
theorem prime_cubic_contribution_le {q : ℕ} [NeZero q]
    (u : ℕ) (hu : 2 ≤ u) (huq : u < q) (minor : Finset (ZMod q))
    (ε : ℝ) (hε : 0 ≤ ε)
    (hbound : ∀ r ∈ minor,
      ‖∑ p ∈ Nat.primesLE u,
        (Real.log (p : ℝ) : ℂ) * ZMod.stdAddChar (r * (p : ZMod q))‖ ≤
          ε * (u : ℝ) / Real.log (u : ℝ)) :
    ‖(∑ r ∈ minor, (∑ p ∈ Nat.primesLE u,
        (Real.log (p : ℝ) : ℂ) * ZMod.stdAddChar (r * (p : ZMod q))) ^ 3 *
          ZMod.stdAddChar (-(r * (u : ZMod q)))) / (q : ℂ)‖ ≤
      ε * Real.log 4 * (u : ℝ) ^ 2 := by
  have hu1 : 1 < (u : ℝ) := by exact_mod_cast (show 1 < u by omega)
  have hlog : 0 < Real.log (u : ℝ) := Real.log_pos hu1
  have hA : 0 ≤ ε * (u : ℝ) / Real.log (u : ℝ) := by positivity
  have h := cubic_character_contribution_le_energy (primeLogWeight u) minor
    (u : ZMod q) (ε * (u : ℝ) / Real.log (u : ℝ)) hA (by
      intro r hr
      rw [residueFourier_primeLogWeight u huq]
      exact hbound r hr)
  simp_rw [residueFourier_primeLogWeight u huq] at h
  rw [primeLogWeight_energy u huq] at h
  apply h.trans
  calc
    ε * (u : ℝ) / Real.log (u : ℝ) *
        (∑ p ∈ Nat.primesLE u, Real.log (p : ℝ) ^ 2) ≤
      ε * (u : ℝ) / Real.log (u : ℝ) *
        (Real.log 4 * (u : ℝ) * Real.log (u : ℝ)) :=
      mul_le_mul_of_nonneg_left (prime_log_squares_le u (by omega)) hA
    _ = ε * Real.log 4 * (u : ℝ) ^ 2 := by
      field_simp

end Problem337.ThreePrimeMinorArc

end

end OAI
