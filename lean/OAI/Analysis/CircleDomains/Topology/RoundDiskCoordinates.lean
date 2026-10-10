import OAI.Analysis.CircleDomains.Topology.MarkedDiskLimits

namespace OAI

/-!
# Euclidean coordinates for bounded round disks

Completing the square for a fractional linear map identifies a round
spherical disk avoiding infinity with an ordinary Euclidean closed
disk. This provides the center/radius coordinates used for marked ends.
-/

open Set Function
open scoped ComplexConjugate

noncomputable section

namespace CircleDomainRigidity

theorem fractional_norm_square_identity (a b c d z : ℂ) :
    ‖((Complex.normSq a - Complex.normSq c : ℝ) : ℂ) * z + (conj a * b - conj c * d)‖ ^ 2 -
      ‖a * d - b * c‖ ^ 2 =
      (Complex.normSq a - Complex.normSq c) * (‖a * z + b‖ ^ 2 - ‖c * z + d‖ ^ 2) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem fractional_norm_region_eq_closedBall
    (a b c d : ℂ) (hA : 0 < Complex.normSq a - Complex.normSq c) :
    {z : ℂ | ‖a * z + b‖ ≤ ‖c * z + d‖} =
      Metric.closedBall (-(conj a * b - conj c * d) / ((Complex.normSq a - Complex.normSq c : ℝ) : ℂ))
        (‖a * d - b * c‖ / (Complex.normSq a - Complex.normSq c)) := by
  let A : ℝ := Complex.normSq a - Complex.normSq c
  let B : ℂ := conj a * b - conj c * d
  have hA' : 0 < A := hA
  have hAc : (A : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
  have hnA : ‖(A : ℂ)‖ = A := by
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA']
  ext z
  change ‖a * z + b‖ ≤ ‖c * z + d‖ ↔ dist z (-B / (A : ℂ)) ≤ ‖a * d - b * c‖ / A
  have he : (A : ℂ) * z + B = (A : ℂ) * (z - -B / (A : ℂ)) := by field_simp; ring
  have hid := fractional_norm_square_identity a b c d z
  change ‖(A : ℂ) * z + B‖ ^ 2 - ‖a * d - b * c‖ ^ 2 =
    A * (‖a * z + b‖ ^ 2 - ‖c * z + d‖ ^ 2) at hid
  have hnorm : ‖(A : ℂ) * z + B‖ = A * dist z (-B / (A : ℂ)) := by
    rw [he, norm_mul, hnA, dist_eq_norm]
  rw [le_div_iff₀ hA, mul_comm (dist z (-B / (A : ℂ))) A, ← hnorm]
  constructor
  · intro h
    have hsq : ‖a * z + b‖ ^ 2 ≤ ‖c * z + d‖ ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    have hp := mul_nonpos_of_nonneg_of_nonpos hA'.le (sub_nonpos.mpr hsq)
    linarith
  · intro h
    have hsq : ‖(A : ℂ) * z + B‖ ^ 2 ≤ ‖a * d - b * c‖ ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h
    have hdif : ‖a * z + b‖ ^ 2 ≤ ‖c * z + d‖ ^ 2 := by nlinarith [hA']
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hdif

end CircleDomainRigidity

end

end OAI
