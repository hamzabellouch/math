import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators ComplexConjugate

namespace Problem337.ThreePrimeMinorEnergy

variable {q : ℕ} [NeZero q]

/-- Transposition for the unnormalized discrete Fourier transform. -/
theorem sum_dft_mul (f g : ZMod q → ℂ) :
    (∑ k, ZMod.dft f k * g k) = ∑ x, f x * ZMod.dft g x := by
  simp only [ZMod.dft_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro k hk
  rw [mul_comm k x]
  ring

/-- Complex conjugation reverses the Fourier frequency. -/
theorem dft_conj (f : ZMod q → ℂ) (k : ZMod q) :
    ZMod.dft (fun x => conj (f x)) k = conj (ZMod.dft f (-k)) := by
  simp only [ZMod.dft_apply, smul_eq_mul, map_sum, map_mul,
    ← AddChar.map_neg_eq_conj]
  apply Finset.sum_congr rfl
  intro x hx
  congr 2
  ring

/-- Exact Parseval identity, retaining the factor `q` for counting measure. -/
theorem dft_parseval (f : ZMod q → ℂ) :
    (∑ k, ‖ZMod.dft f k‖ ^ 2) = (q : ℝ) * ∑ x, ‖f x‖ ^ 2 := by
  have h := sum_dft_mul f (fun k => conj (ZMod.dft f k))
  have hconj (x : ZMod q) :
      ZMod.dft (fun k => conj (ZMod.dft f k)) x = (q : ℂ) * conj (f x) := by
    rw [dft_conj]
    simp only [ZMod.dft_dft, neg_neg, smul_eq_mul, map_mul, map_natCast]
  simp only [hconj] at h
  have h' : (∑ k, (‖ZMod.dft f k‖ ^ 2 : ℂ)) =
      (q : ℂ) * ∑ x, (‖f x‖ ^ 2 : ℂ) := by
    calc
      (∑ k, (‖ZMod.dft f k‖ ^ 2 : ℂ)) =
          ∑ k, ZMod.dft f k * conj (ZMod.dft f k) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
      _ = ∑ x, f x * ((q : ℂ) * conj (f x)) := h
      _ = (q : ℂ) * ∑ x, (‖f x‖ ^ 2 : ℂ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        rw [← mul_assoc, mul_comm (f x) (q : ℂ), mul_assoc,
          Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  exact_mod_cast h'

/-- The cubic contribution of any frequency set is controlled by its
supremum Fourier bound and the exact input energy. The phase may be any
function of modulus at most one, so either Fourier sign convention is allowed. -/
theorem minor_cubic_bound (f phase : ZMod q → ℂ) (minor : Finset (ZMod q))
    (B : ℝ) (hB : 0 ≤ B)
    (hminor : ∀ k ∈ minor, ‖ZMod.dft f k‖ ≤ B)
    (hphase : ∀ k ∈ minor, ‖phase k‖ ≤ 1) :
    ‖(q : ℂ)⁻¹ * ∑ k ∈ minor, ZMod.dft f k ^ 3 * phase k‖ ≤
      B * ∑ x, ‖f x‖ ^ 2 := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hsum : ‖∑ k ∈ minor, ZMod.dft f k ^ 3 * phase k‖ ≤
      B * ((q : ℝ) * ∑ x, ‖f x‖ ^ 2) := by
    calc
      ‖∑ k ∈ minor, ZMod.dft f k ^ 3 * phase k‖ ≤
          ∑ k ∈ minor, ‖ZMod.dft f k ^ 3 * phase k‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ minor, B * ‖ZMod.dft f k‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro k hk
        rw [norm_mul, norm_pow]
        calc
          ‖ZMod.dft f k‖ ^ 3 * ‖phase k‖ ≤ ‖ZMod.dft f k‖ ^ 3 := by
            simpa using mul_le_mul_of_nonneg_left (hphase k hk) (by positivity :
              0 ≤ ‖ZMod.dft f k‖ ^ 3)
          _ ≤ B * ‖ZMod.dft f k‖ ^ 2 := by
            nlinarith [mul_le_mul_of_nonneg_right (hminor k hk)
              (sq_nonneg ‖ZMod.dft f k‖)]
      _ = B * ∑ k ∈ minor, ‖ZMod.dft f k‖ ^ 2 := (Finset.mul_sum ..).symm
      _ ≤ B * ∑ k, ‖ZMod.dft f k‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hB
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (by intros; positivity)
      _ = B * ((q : ℝ) * ∑ x, ‖f x‖ ^ 2) := by rw [dft_parseval]
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc
    (q : ℝ)⁻¹ * ‖∑ k ∈ minor, ZMod.dft f k ^ 3 * phase k‖ ≤
        (q : ℝ)⁻¹ * (B * ((q : ℝ) * ∑ x, ‖f x‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hq.le)
    _ = B * ∑ x, ‖f x‖ ^ 2 := by field_simp

end Problem337.ThreePrimeMinorEnergy

end

end OAI
