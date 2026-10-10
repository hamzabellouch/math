import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Data.Int.GCD
import OAI.NumberTheory.Ostmann.Preliminaries.PhaseDistance

namespace OAI

/-! # Separation of the phases in a short block near a reduced rational -/

namespace Ostmann

/-- Dirichlet approximation in exactly the form needed by quadratic
Weyl differencing; the numerator and denominator are reduced. -/
theorem exists_reduced_phase_approximation (θ : ℝ) (Q : ℕ) (hQ : 0 < Q) :
    ∃ (a : ℤ) (r : ℕ), 0 < r ∧ r ≤ Q ∧ a.natAbs.Coprime r ∧
      |θ - (a : ℝ) / r| ≤ 1 / (((Q : ℝ) + 1) * r) ∧
      |θ - (a : ℝ) / r| ≤ 1 / (r : ℝ) ^ 2 := by
  obtain ⟨q, hq, hqQ⟩ := Real.exists_rat_abs_sub_le_and_den_le θ hQ
  have hr : (0 : ℝ) < q.den := by exact_mod_cast q.pos
  have hQ' : (q.den : ℝ) ≤ Q := by exact_mod_cast hqQ
  have hcast : (q : ℝ) = (q.num : ℝ) / q.den := by exact Rat.cast_def q
  refine ⟨q.num, q.den, q.pos, hqQ, q.reduced, ?_, ?_⟩
  · simpa only [hcast] using hq
  · apply (show |θ - (q.num : ℝ) / q.den| ≤ 1 / (((Q : ℝ) + 1) * q.den) by
      simpa only [hcast] using hq).trans
    apply one_div_le_one_div_of_le (by positivity : 0 < (q.den : ℝ) ^ 2)
    nlinarith

/-- A nonzero short shift cannot be too close to any integer. This is the
separation claim used inside each block of length at most r/2. -/
theorem rational_phase_shift_separation (θ : ℝ) (a δ k : ℤ) (r : ℕ)
    (hr : 0 < r) (hcop : a.natAbs.Coprime r) (hδ : δ ≠ 0)
    (hshort : 2 * |(δ : ℝ)| ≤ r)
    (happrox : |θ - (a : ℝ) / r| ≤ 1 / (r : ℝ) ^ 2) :
    1 / (2 * (r : ℝ)) ≤ |(δ : ℝ) * θ - k| := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hn : δ * a - (r : ℤ) * k ≠ 0 := by
    intro heq
    have heq' : δ * a = (r : ℤ) * k := sub_eq_zero.mp heq
    have hd : r ∣ δ.natAbs * a.natAbs := by
      refine ⟨k.natAbs, ?_⟩
      simpa only [Int.natAbs_mul, Int.natAbs_natCast] using congrArg Int.natAbs heq'
    have hdδ : r ∣ δ.natAbs := hcop.symm.dvd_of_dvd_mul_right hd
    have hle : r ≤ δ.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hδ) hdδ
    have hleR : (r : ℝ) ≤ |(δ : ℝ)| := by
      have hh : (r : ℝ) ≤ δ.natAbs := by exact_mod_cast hle
      simpa only [Nat.cast_natAbs, Int.cast_abs] using hh
    linarith
  have hnon : (1 : ℝ) ≤ |((δ * a - (r : ℤ) * k : ℤ) : ℝ)| := by
    have hh : (1 : ℝ) ≤ (δ * a - (r : ℤ) * k).natAbs := by
      exact_mod_cast Int.natAbs_pos.mpr hn
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hh
  have heq : ((δ * a - (r : ℤ) * k : ℤ) : ℝ) =
      (r : ℝ) * ((δ : ℝ) * θ - k) - (r : ℝ) * δ * (θ - (a : ℝ) / r) := by
    push_cast
    field_simp
    ring
  have habs : |(r : ℝ) * ((δ : ℝ) * θ - k) -
      (r : ℝ) * δ * (θ - (a : ℝ) / r)| ≤
      |(r : ℝ) * ((δ : ℝ) * θ - k)| +
        |(r : ℝ) * δ * (θ - (a : ℝ) / r)| := by
    simpa only [sub_eq_add_neg, abs_neg] using
      abs_add_le ((r : ℝ) * ((δ : ℝ) * θ - k))
        (-((r : ℝ) * δ * (θ - (a : ℝ) / r)))
  rw [← heq] at habs
  simp only [abs_mul, abs_of_pos hrR] at habs
  have herr := mul_le_mul_of_nonneg_left happrox
    (show 0 ≤ (r : ℝ) * |(δ : ℝ)| by positivity)
  have hratio : (r : ℝ) * |(δ : ℝ)| * (1 / (r : ℝ) ^ 2) = |(δ : ℝ)| / r := by
    field_simp
  rw [hratio] at herr
  have hhalf : |(δ : ℝ)| / r ≤ 1 / 2 := (div_le_iff₀ hrR).mpr (by linarith)
  apply (div_le_iff₀ (show 0 < 2 * (r : ℝ) by positivity)).mpr
  nlinarith

end Ostmann

end OAI
