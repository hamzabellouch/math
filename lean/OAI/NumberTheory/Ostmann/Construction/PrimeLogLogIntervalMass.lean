import OAI.NumberTheory.Ostmann.Preliminaries.MertensPrimeBands
import OAI.NumberTheory.Ostmann.Construction.RichSubintervals

namespace OAI

/-! # Uniform harmonic mass bounds in the iterated-log coordinate

Only the upper half of the already recorded Mertens input is needed here.
The constant need not be sharp: a uniform density ceiling suffices for the
finite density-increment selection.
-/

namespace Ostmann

open scoped BigOperators Classical

theorem prime_loglog_unit_mass_upper {C : ℝ} (hM : MertensEstimate C)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (a : ℝ) (ha : max C 0 ≤ a) :
    weightedIntervalMass P (fun p => Real.log (Real.log p)) (fun p => (p : ℝ)⁻¹)
      a (a + 1) ≤ Real.exp 1 + 1 := by
  let S := P.filter (fun p : ℕ => a < Real.log (Real.log (p : ℝ)) ∧
    Real.log (Real.log (p : ℝ)) ≤ a + 1)
  let Q := ⌊Real.exp (Real.exp (a + 1))⌋₊
  have hQ : 1 ≤ Q := (Nat.one_le_floor_iff _).mpr (Real.one_le_exp (Real.exp_nonneg _))
  have hsub : S ⊆ Nat.primesLE Q := by
    intro p hp
    obtain ⟨hp, hlo, hhi⟩ := Finset.mem_filter.mp hp
    have hprime := hP p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hprime.one_lt)
    have hlogup : Real.log p ≤ Real.exp (a + 1) := (Real.log_le_iff_le_exp hlog).mp hhi
    have hpup : (p : ℝ) ≤ Real.exp (Real.exp (a + 1)) :=
      (Real.log_le_iff_le_exp hp0).mp hlogup
    exact Nat.mem_primesLE.mpr ⟨Nat.le_floor hpup, hprime⟩
  have hlogQ : Real.log (Q : ℝ) ≤ Real.exp (a + 1) := by
    have hQpos : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
    have h := Real.log_le_log hQpos (Nat.floor_le (Real.exp_nonneg (Real.exp (a + 1))))
    simpa only [Real.log_exp] using h
  have hweight : (∑ p ∈ S, Real.log (p : ℝ) / p) ≤ Real.exp (a + 1) + C := by
    apply le_trans _ ((hM.upper Q hQ).trans (by linarith : Real.log Q + C ≤ Real.exp (a + 1) + C))
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro p _ _
    exact div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
  have hmul : Real.exp a * (∑ p ∈ S, (p : ℝ)⁻¹) ≤
      ∑ p ∈ S, Real.log (p : ℝ) / p := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨hp, hlo, _⟩ := Finset.mem_filter.mp hp
    have hprime := hP p hp
    have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hprime.one_lt)
    have he : Real.exp a ≤ Real.log (p : ℝ) :=
      ((Real.lt_log_iff_exp_lt hlog).mp hlo).le
    simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_right he (by positivity : 0 ≤ (p : ℝ)⁻¹)
  have hC : C ≤ Real.exp a := by
    have hc := (le_max_left C 0).trans ha
    linarith [Real.add_one_le_exp a]
  change (∑ p ∈ S, (p : ℝ)⁻¹) ≤ _
  rw [Real.exp_add] at hweight
  nlinarith [Real.exp_pos a]

/-- This applies to every subset of the primes, uniformly in its choice. -/
theorem prime_loglog_interval_mass_upper {C : ℝ} (hM : MertensEstimate C)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (a b : ℝ) (ha : max C 0 ≤ a) (hab : a ≤ b) :
    weightedIntervalMass P (fun p => Real.log (Real.log p)) (fun p => (p : ℝ)⁻¹)
      a b ≤ (Real.exp 1 + 1) * (b - a + 1) := by
  let φ := weightedCDF P (fun p => Real.log (Real.log p)) (fun p => (p : ℝ)⁻¹)
  have hmono : Monotone φ := weightedCDF_mono _ _ _ (by intros; positivity)
  have h := cdf_interval_upper φ hmono (max C 0) (Real.exp 1 + 1) (by positivity)
    (by
      intro u hu
      rw [weightedCDF_sub _ _ _ u (u + 1) (by linarith)]
      exact prime_loglog_unit_mass_upper hM P hP u hu) a b ha hab
  rwa [weightedCDF_sub _ _ _ a b hab] at h

end Ostmann

end OAI
