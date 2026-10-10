import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ZeroTailDeterminantPolynomial
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.SeparatorScaling

namespace OAI

/-! # Simplicity and axis exclusion for the unscaled certificate polynomial -/

open Polynomial

namespace DefocusingNLS.SeparatorArithmetic

attribute [local irreducible] scaledSeparatorPolynomial windingPolynomial

theorem windingPolynomial_complex_ne_zero (ell : Fin 4) :
    (windingPolynomial ell).map (Int.castRingHom ℂ) ≠ 0 := by
  intro h
  apply scaledSeparatorPolynomial_complex_ne_zero ell
  rw [scaledSeparatorPolynomial_identity, h, zero_comp, mul_zero]

theorem scaledSeparatorPolynomial_roots_nodup (ell : Fin 4) :
    ((scaledSeparatorPolynomial ell).map GaussianInt.toComplex).roots.Nodup := by
  obtain ⟨z, _, _, hz⟩ := roots_of_fifteen_disks
    ((scaledSeparatorPolynomial ell).map GaussianInt.toComplex)
    (scaledSeparatorPolynomial_complex_ne_zero ell)
    (natDegree_map_le.trans (scaledSeparatorPolynomial_degree ell))
    (fun j => (diskCenters ell j : ℂ)) 100
    (complex_disk_centers_separated ell) (root_in_certified_disk ell)
  rw [hz]
  exact Finset.nodup _

theorem windingPolynomial_roots_nodup (ell : Fin 4) :
    ((windingPolynomial ell).map (Int.castRingHom ℂ)).roots.Nodup := by
  have h := scaledSeparatorPolynomial_roots_nodup ell
  rw [scaledSeparatorPolynomial_roots] at h
  exact Multiset.Nodup.of_map _ h

theorem windingPolynomial_no_axis_root (ell : Fin 4) {z : ℂ}
    (hz : ((windingPolynomial ell).map (Int.castRingHom ℂ)).IsRoot z) : z.re ≠ 0 := by
  have hscaled : ((scaledSeparatorPolynomial ell).map GaussianInt.toComplex).IsRoot
      ((diskScale : ℂ) * z) := by
    rw [Polynomial.IsRoot, scaledSeparatorPolynomial_identity]
    simp only [eval_mul, eval_C, eval_comp, eval_X]
    rw [inv_mul_cancel_left₀ (by norm_num [diskScale]), hz.eq_zero, mul_zero]
  have hn := zero_tail_no_axis_zero ell hscaled
  intro h
  apply hn
  simp [Complex.mul_re, h]

end DefocusingNLS.SeparatorArithmetic

end OAI
