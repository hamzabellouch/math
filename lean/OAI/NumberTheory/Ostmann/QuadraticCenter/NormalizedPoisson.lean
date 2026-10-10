import OAI.NumberTheory.Ostmann.QuadraticCenter.FrequencySymmetry
import OAI.NumberTheory.Ostmann.QuadraticCenter.GaussNormalization

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open Ostmann.QuadraticSieve
open scoped BigOperators FourierTransform SchwartzMap

theorem dft_eq_sqrt_mul_unitary {d : ℕ} [NeZero d] (G : ZMod d → ℂ) (v : ZMod d) :
    ZMod.dft G v = (Real.sqrt d : ℂ) * Supply.unitaryDFT G v := by
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_neZero d
  have hs : (Real.sqrt d : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hd).ne'
  simp only [Supply.unitaryDFT]
  field_simp

def normalizedQuadraticTransform (q d : ℕ) [NeZero d] (G : ZMod d → ℂ)
    (mInv : ZMod d) (a R : ℝ) : ℂ :=
  (jacobiSym (d : ℤ) q : ℂ) / (Real.sqrt (R * d) : ℂ) *
    ∑' u : ℤ, quadraticFourierFrequency q d G mInv a R u

theorem weighted_poisson_eq_normalized {q d : ℕ} [NeZero q] [NeZero d]
    (hqd : q.Coprime d) (hq : Odd q) (hsq : Squarefree q)
    (r s t h : ℤ) (hbez : (d : ℤ) * r + (q : ℤ) * s = 1)
    (hc : (d : ℤ) ∣ t + (q : ℤ) * h) {X : ℝ} (hX : 0 < X) (G : ZMod d → ℂ) :
    (∑' n : ℤ, (jacobiSym (n - t) q : ℂ) * G (n : ZMod d) *
      SchwartzCutoff.psi ((n : ℝ) / X)) / (Real.sqrt X : ℂ) =
      quadraticGaussUnit q * normalizedQuadraticTransform q d G (q : ZMod d)⁻¹
        ((t : ℝ) / q + h) ((q : ℝ) / X) := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_neZero q
  have hdr : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_neZero d
  rw [weighted_translated_quadratic_poisson hqd hq hsq r s hbez X hX t G SchwartzCutoff.psi]
  have hu (u : ℤ) :
      (jacobiSym (u * r) q : ℂ) *
        ZMod.stdAddChar (((u * r : ℤ) : ZMod q) * (t : ZMod q)) *
        ZMod.dft G (-((u * s : ℤ) : ZMod d)) *
        𝓕 SchwartzCutoff.psi ((u : ℝ) * X / (q * d)) =
      ((jacobiSym (d : ℤ) q : ℂ) * (Real.sqrt d : ℂ)) *
        quadraticFourierFrequency q d G (q : ZMod d)⁻¹
          ((t : ℝ) / q + h) ((q : ℝ) / X) u := by
    rw [jacobi_mul_bezout_inverse r s u hbez, Int.cast_mul,
      stdAddChar_common_center r s t h u hbez hc, dft_eq_sqrt_mul_unitary]
    have hv : -((u * s : ℤ) : ZMod d) = -(u : ZMod d) * (q : ZMod d)⁻¹ := by
      rw [Int.cast_mul, bezout_inverse_cast hqd r s hbez, neg_mul]
    have hx : (u : ℝ) * X / (q * d) = (u : ℝ) / (((q : ℝ) / X) * d) := by field_simp
    rw [hv, hx]
    unfold quadraticFourierFrequency cutoffFourier
    ring
  simp_rw [hu]
  rw [tsum_mul_left]
  have hsc : ((X / ((q : ℝ) * d) : ℝ) : ℂ) * (Real.sqrt d : ℂ) / (Real.sqrt X : ℂ) =
      1 / (Real.sqrt q : ℂ) / (Real.sqrt (((q : ℝ) / X) * d) : ℂ) := by
    exact_mod_cast poisson_scale_scalar hX hqr hdr
  calc
    _ = (((X / ((q : ℝ) * d) : ℝ) : ℂ) * (Real.sqrt d : ℂ) / (Real.sqrt X : ℂ)) *
        gaussSum (jacobiDirichletCharacter q) ZMod.stdAddChar *
        (jacobiSym (d : ℤ) q : ℂ) *
        (∑' u : ℤ, quadraticFourierFrequency q d G (q : ZMod d)⁻¹
          ((t : ℝ) / q + h) ((q : ℝ) / X) u) := by ring
    _ = _ := by
      rw [hsc]
      unfold quadraticGaussUnit normalizedQuadraticTransform
      ring

end Ostmann.QuadraticCenter

end

end OAI
