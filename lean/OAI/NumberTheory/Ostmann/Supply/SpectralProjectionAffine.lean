import OAI.NumberTheory.Ostmann.Supply.SpectralProjectionPairing

namespace OAI

/-! # Affine identities for the constant-killing local projection -/

namespace Ostmann
open scoped Classical BigOperators

theorem densityFourier_affine {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (a c : ℂ) (b : ZMod p) :
    densityFourier (fun x => a * f x + c) b =
      a * densityFourier f b + densityFourier (fun _ => c) b := by
  simp only [densityFourier, additiveFourier_apply, add_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, mul_assoc]
  ring

theorem finiteSpectralProjection_affine {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (hE : 0 ∉ E) (f : ZMod p → ℂ) (a c : ℂ) :
    finiteSpectralProjection E (fun x => a * f x + c) =
      fun x => a * finiteSpectralProjection E f x := by
  have he : densityFourier (finiteSpectralProjection E (fun x => a * f x + c)) =
      densityFourier (fun x => a * finiteSpectralProjection E f x) := by
    funext b
    rw [finiteSpectralProjection_fourier, densityFourier_affine,
      densityFourier_const_mul, finiteSpectralProjection_fourier]
    by_cases hb : b ∈ E
    · have hb0 : b ≠ 0 := by intro h; subst b; exact hE hb
      simp only [ite_eq_left hb, densityFourier, additiveFourier_const,
        ite_eq_right hb0, mul_zero, add_zero]
    · simp only [ite_eq_right hb, mul_zero]
  have hh := congrArg (fun g => fun x => densityFourierInverse g x) he
  simpa only [densityFourierInverse_fourier] using hh

end Ostmann

end OAI
