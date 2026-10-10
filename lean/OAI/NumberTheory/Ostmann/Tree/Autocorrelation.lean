import OAI.NumberTheory.Ostmann.Tree.AffineFourier

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [NeZero p]

def autocorrelation (f : ZMod p → ℂ) (d : ZMod p) : ℂ :=
  mean (fun x => f x*conj (f (x-d)))

theorem fourier_conj_sub (f : ZMod p → ℂ) (x a : ZMod p) :
    fourier (fun d => conj (f (x-d))) a =
      ZMod.stdAddChar (-(a*x))*conj (fourier f a) := by
  have h := fourier_affine (fun d => conj (f d)) (-1 : (ZMod p)ˣ) x a
  simp only [inv_neg, inv_one, Units.val_neg, Units.val_one,
    neg_mul, one_mul, ← conj_fourier] at h
  convert h using 1
  congr 1
  funext d
  congr 2
  ring

theorem fourier_autocorrelation (f : ZMod p → ℂ) (a : ZMod p) :
    fourier (autocorrelation f) a = (‖fourier f a‖^2 : ℂ) := by
  unfold autocorrelation mean
  rw [fourier_const_mul, fourier_sum]
  simp_rw [fourier_const_mul, fourier_conj_sub]
  calc
    _ = ((p:ℂ)⁻¹ * ∑ x, f x*ZMod.stdAddChar (-(a*x))) * conj (fourier f a) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = fourier f a * conj (fourier f a) := by rw [fourier_apply]
    _ = _ := Complex.mul_conj' _

@[simp] theorem autocorrelation_zero (f : ZMod p → ℂ) :
    autocorrelation f 0 = (l2Sq f : ℂ) := by
  simp only [autocorrelation, sub_zero, mean, l2Sq, Complex.mul_conj']
  push_cast
  rfl

theorem autocorrelation_spectral_mass (f : ZMod p → ℂ) :
    ∑ a : ZMod p, ‖fourier f a‖^2 = l2Sq f := fourier_parseval f

end
end Ostmann.FiniteField

end OAI
