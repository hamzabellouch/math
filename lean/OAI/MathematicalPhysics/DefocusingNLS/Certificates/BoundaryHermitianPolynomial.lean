import OAI.MathematicalPhysics.DefocusingNLS.Certificates.BoundaryPolynomial
import Mathlib.Algebra.Polynomial.Eval.Degree

namespace OAI

/-! # Hermitian polynomial and its reflected boundary sum -/

open Polynomial Matrix

namespace DefocusingNLS

noncomputable def conjugatePolynomial (p : Polynomial ℂ) : Polynomial ℂ :=
  p.map (starRingEnd ℂ)

noncomputable def sharpPolynomial (p : Polynomial ℂ) : Polynomial ℂ :=
  (conjugatePolynomial p).comp (C (-1) * X)

theorem coeff_conjugatePolynomial (p : Polynomial ℂ) (n : ℕ) :
    (conjugatePolynomial p).coeff n = star (p.coeff n) := by
  simp [conjugatePolynomial]

theorem coeff_sharpPolynomial (p : Polynomial ℂ) (n : ℕ) :
    (sharpPolynomial p).coeff n = star (p.coeff n) * (-1) ^ n := by
  rw [sharpPolynomial, comp_C_mul_X_coeff, coeff_conjugatePolynomial]

theorem conjugatePolynomial_degree (p : Polynomial ℂ) :
    (conjugatePolynomial p).natDegree ≤ p.natDegree := natDegree_map_le

theorem sharpPolynomial_degree (p : Polynomial ℂ) :
    (sharpPolynomial p).natDegree ≤ p.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [coeff_sharpPolynomial, coeff_eq_zero_of_natDegree_lt hn, star_zero, zero_mul]

noncomputable def hermitianPolynomial (M : ℝ) (s : ℂ)
    (T : Matrix (Fin 2) (Fin 2) (Polynomial ℂ)) (i j : Fin 2) : Polynomial ℂ :=
  C (M : ℂ) * conjugatePolynomial (T 0 i) * T 0 j +
    C s * (conjugatePolynomial (T 0 i) * T 1 j - conjugatePolynomial (T 1 i) * T 0 j)

theorem hermitianPolynomial_degree (M : ℝ) (s : ℂ)
    (T : Matrix (Fin 2) (Fin 2) (Polynomial ℂ)) (K : ℕ)
    (hT : ∀ i j, (T i j).natDegree ≤ K) (i j : Fin 2) :
    (hermitianPolynomial M s T i j).natDegree ≤ 2 * K := by
  have hp (a b c d : Fin 2) :
      (conjugatePolynomial (T a b) * T c d).natDegree ≤ 2 * K := by
    exact natDegree_mul_le.trans ((add_le_add
      ((conjugatePolynomial_degree _).trans (hT a b)) (hT c d)).trans (by omega))
  apply natDegree_add_le_of_degree_le
  · simpa only [mul_assoc] using
      (natDegree_C_mul_le (M : ℂ) (conjugatePolynomial (T 0 i) * T 0 j)).trans (hp ..)
  · exact (natDegree_C_mul_le _ _).trans
      ((natDegree_sub_le_of_le (hp 0 i 1 j) (hp 1 i 0 j)).trans (by simp))

theorem hermitianPolynomial_top (M : ℝ) (s : ℂ)
    (T : Matrix (Fin 2) (Fin 2) (Polynomial ℂ)) (K : ℕ)
    (hT : ∀ i j, (T i j).natDegree ≤ K) (i j : Fin 2) :
    (hermitianPolynomial M s T i j).coeff (2 * K) =
      forwardFormEntry M s (fun a b => (T a b).coeff K) i j := by
  have hc (a b c d : Fin 2) :
      (conjugatePolynomial (T a b) * T c d).coeff (2 * K) =
        star ((T a b).coeff K) * (T c d).coeff K := by
    rw [show 2 * K = K + K by omega, coeff_mul_add_eq_of_natDegree_le
      ((conjugatePolynomial_degree _).trans (hT a b)) (hT c d), coeff_conjugatePolynomial]
  simp only [hermitianPolynomial, mul_assoc, coeff_add, coeff_C_mul, coeff_sub, hc,
    forwardFormEntry]

noncomputable def reflectedHermitianPolynomial (M : ℝ) (s : ℂ)
    (T : Matrix (Fin 2) (Fin 2) (Polynomial ℂ)) (i j : Fin 2) : Polynomial ℂ :=
  hermitianPolynomial M s T i j + sharpPolynomial (hermitianPolynomial M s T i j)

theorem reflectedHermitianPolynomial_degree (M : ℝ) (s : ℂ)
    (T : Matrix (Fin 2) (Fin 2) (Polynomial ℂ)) (K : ℕ)
    (hT : ∀ i j, (T i j).natDegree ≤ K) (i j : Fin 2) :
    (reflectedHermitianPolynomial M s T i j).natDegree ≤ 2 * K :=
  natDegree_add_le_of_degree_le (hermitianPolynomial_degree M s T K hT i j)
    ((sharpPolynomial_degree _).trans (hermitianPolynomial_degree M s T K hT i j))

theorem reflectedHermitianPolynomial_coefficient (M : ℝ) (s : ℂ)
    (T : Matrix (Fin 2) (Fin 2) (Polynomial ℂ)) (i j : Fin 2) (n : ℕ) :
    (reflectedHermitianPolynomial M s T i j).coeff n =
      (hermitianPolynomial M s T i j).coeff n +
        star ((hermitianPolynomial M s T i j).coeff n) * (-1) ^ n := by
  simp only [reflectedHermitianPolynomial, coeff_add, coeff_sharpPolynomial]

end DefocusingNLS

end OAI
