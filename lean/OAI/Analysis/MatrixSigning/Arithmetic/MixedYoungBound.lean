import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.ScalarPsi

namespace OAI

open Matrix

namespace CurrentKS.Scalar

lemma mixed_young_bound {c s k f h p q a b u v r w : ℝ}
    (hc : 0 ≤ c) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hf : f^2/s ≤ k/2)
    (hu : 2*(f*h)*u ≤ s*r + (f*h)^2/s*a)
    (hv : 2*(f*h)*v ≤ s*w + (f*h)^2/s*b) :
    2*c*f*h*(p*v+q*u) ≤ c*s*(q*r+p*w) + (c/2)*k*h^2*(b*p+a*q) := by
  have hh : (f*h)^2/s ≤ (k/2)*h^2 := by
    calc
      _ = (f^2/s)*h^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hf (sq_nonneg h)
  have ha' := mul_le_mul_of_nonneg_right hh ha
  have hb' := mul_le_mul_of_nonneg_right hh hb
  have hu' : 2*(f*h)*u ≤ s*r + (k/2)*h^2*a := hu.trans (add_le_add (le_refl (s*r)) ha')
  have hv' : 2*(f*h)*v ≤ s*w + (k/2)*h^2*b := hv.trans (add_le_add (le_refl (s*w)) hb')
  have hu'' := mul_le_mul_of_nonneg_left hu' (mul_nonneg hc hq)
  have hv'' := mul_le_mul_of_nonneg_left hv' (mul_nonneg hc hp)
  nlinarith

lemma derivative_square_le {x : ℝ} (hx : |x| < 1) : psi₁ x^2 / psi x ≤ kappa x/2 := by
  have hh := derivative_ratio_le hx
  rw [← div_div,div_le_iff₀ (kappa_pos hx)] at hh
  linarith
end CurrentKS.Scalar

end OAI
