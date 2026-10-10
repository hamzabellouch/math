import OAI.NumberTheory.JointDickman.Arithmetic.MovingPrimeIndependence

namespace OAI

/-! # The finite Hilbert estimates for residue profiles

Only uniform finite residue means are needed for the profile-preservation
argument. Their compatible refinements replace an explicit construction of
Haar measure on the profinite integers.
-/

namespace JointDickman
open Finset

noncomputable def residueEnergy {q : ℕ} [NeZero q] (f : ZMod q → ℂ) : ℝ :=
  (∑ a, ‖f a‖ ^ 2) / (q : ℝ)

noncomputable def residueLift {d q : ℕ} (f : ZMod d → ℂ) (a : ZMod q) : ℂ :=
  f (a.val : ZMod d)

theorem residueEnergy_nonneg {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    0 ≤ residueEnergy f := div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg _)

theorem residueMean_lift {d q : ℕ} [NeZero d] [NeZero q]
    (hd : d ∣ q) (f : ZMod d → ℂ) : residueMean (residueLift (q := q) f) = residueMean f := by
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
  have hc (a x : ℝ) (hx : x ≠ 0) : a*x/(x*x) = a/x := by field_simp
  apply Complex.ext
  · simpa [residueMean, residueLift, Complex.div_re, Complex.normSq, hc _ _ hq, hc _ _ hd0] using
      residue_quotient_mean hd (fun a => (f a).re)
  · simpa [residueMean, residueLift, Complex.div_im, Complex.normSq, hc _ _ hq, hc _ _ hd0] using
      residue_quotient_mean hd (fun a => (f a).im)

theorem residueEnergy_lift {d q : ℕ} [NeZero d] [NeZero q]
    (hd : d ∣ q) (f : ZMod d → ℂ) :
    residueEnergy (residueLift (q := q) f) = residueEnergy f :=
  residue_quotient_mean hd (fun a => ‖f a‖ ^ 2)

theorem residueMean_mul_norm_sq {q : ℕ} [NeZero q] (f g : ZMod q → ℂ) :
    ‖residueMean (fun a => f a * g a)‖ ^ 2 ≤ residueEnergy f * residueEnergy g := by
  have hn := norm_sum_le (univ : Finset (ZMod q)) (fun a => f a * g a)
  simp only [norm_mul] at hn
  have hs := sum_mul_sq_le_sq_mul_sq (univ : Finset (ZMod q))
    (fun a => ‖f a‖) (fun a => ‖g a‖)
  have hsq : ‖∑ a, f a * g a‖ ^ 2 ≤
      (∑ a, ‖f a‖ ^ 2) * (∑ a, ‖g a‖ ^ 2) :=
    (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hs
  unfold residueMean residueEnergy
  rw [norm_div, Complex.norm_natCast, div_pow, div_mul_div_comm]
  simpa only [pow_two] using div_le_div_of_nonneg_right hsq (sq_nonneg (q : ℝ))

theorem residueMean_mul_norm_le {q : ℕ} [NeZero q] (f g : ZMod q → ℂ) :
    ‖residueMean (fun a => f a * g a)‖ ≤
      Real.sqrt (residueEnergy f * residueEnergy g) :=
  Real.le_sqrt_of_sq_le (residueMean_mul_norm_sq f g)

end JointDickman

end OAI
