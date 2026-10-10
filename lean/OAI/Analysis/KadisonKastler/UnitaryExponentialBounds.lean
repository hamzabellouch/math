import OAI.Analysis.KadisonKastler.Algebra
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Star

namespace OAI

/-! # A quantitative exponential bound for the normalizer path argument -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private def exponentialPath (h : selfAdjoint (H →L[ℂ] H)) (t : ℝ) :
    unitary (H →L[ℂ] H) := selfAdjoint.expUnitary (t • h)

private theorem exponentialPath_deriv (h : selfAdjoint (H →L[ℂ] H)) (t : ℝ) :
    HasDerivAt (fun s => (exponentialPath h s : H →L[ℂ] H))
      ((exponentialPath h t : H →L[ℂ] H) * (Complex.I • (h : H →L[ℂ] H))) t := by
  have he (s : ℝ) : (exponentialPath h s : H →L[ℂ] H) =
      NormedSpace.exp (s • (Complex.I • (h : H →L[ℂ] H))) := by
    change NormedSpace.exp (Complex.I • (s • (h : H →L[ℂ] H))) = _
    rw [smul_comm Complex.I s]
  simp_rw [he]
  exact hasDerivAt_exp_smul_const (Complex.I • (h : H →L[ℂ] H)) t

private theorem exponentialPath_deriv_left (h : selfAdjoint (H →L[ℂ] H)) (t : ℝ) :
    HasDerivAt (fun s => (exponentialPath h s : H →L[ℂ] H))
      ((Complex.I • (h : H →L[ℂ] H)) * (exponentialPath h t : H →L[ℂ] H)) t := by
  have he (s : ℝ) : (exponentialPath h s : H →L[ℂ] H) =
      NormedSpace.exp (s • (Complex.I • (h : H →L[ℂ] H))) := by
    change NormedSpace.exp (Complex.I • (s • (h : H →L[ℂ] H))) = _
    rw [smul_comm Complex.I s]
  simp_rw [he]
  exact hasDerivAt_exp_smul_const' (Complex.I • (h : H →L[ℂ] H)) t

theorem norm_expUnitary_sub_expUnitary_le (h k : selfAdjoint (H →L[ℂ] H)) :
    ‖(selfAdjoint.expUnitary h : H →L[ℂ] H) - selfAdjoint.expUnitary k‖ ≤
      ‖(h : H →L[ℂ] H) - k‖ := by
  let f (t : ℝ) := (exponentialPath h t : H →L[ℂ] H) * exponentialPath k (1 - t)
  let f' (t : ℝ) := (exponentialPath h t : H →L[ℂ] H) *
    (Complex.I • ((h : H →L[ℂ] H) - k)) * exponentialPath k (1 - t)
  have hf (t : ℝ) : HasDerivAt f (f' t) t := by
    have hk := (exponentialPath_deriv_left k (1 - t)).scomp t
      ((hasDerivAt_id t).const_sub (1 : ℝ))
    have hd := (exponentialPath_deriv h t).mul hk
    convert hd using 1 <;>
      simp only [f, f', Function.comp_apply, one_smul, neg_smul, smul_sub] <;> noncomm_ring
  have hn (t : ℝ) : ‖f' t‖ ≤ ‖(h : H →L[ℂ] H) - k‖ := by
    dsimp [f']
    rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
      norm_smul, Complex.norm_I, one_mul]
  have hb := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (hf t).hasDerivWithinAt) (fun t _ => hn t)
  have hzero (a : selfAdjoint (H →L[ℂ] H)) :
      (exponentialPath a 0 : H →L[ℂ] H) = 1 := by
    change NormedSpace.exp (Complex.I • ((0 : ℝ) • (a : H →L[ℂ] H))) = 1
    rw [zero_smul, smul_zero, NormedSpace.exp_zero]
  have hone (a : selfAdjoint (H →L[ℂ] H)) :
      exponentialPath a 1 = selfAdjoint.expUnitary a := by
    apply Subtype.ext
    change NormedSpace.exp (Complex.I • ((1 : ℝ) • (a : H →L[ℂ] H))) = _
    rw [one_smul]
    rfl
  simpa only [f, sub_self, sub_zero, hzero, hone, one_mul, mul_one] using hb

private theorem exponentialPath_zero (h : selfAdjoint (H →L[ℂ] H)) :
    exponentialPath h 0 = 1 := by
  apply Subtype.ext
  change NormedSpace.exp (Complex.I • ((0 : ℝ) • (h : H →L[ℂ] H))) = 1
  rw [zero_smul, smul_zero, NormedSpace.exp_zero]

private theorem exponentialPath_one (h : selfAdjoint (H →L[ℂ] H)) :
    exponentialPath h 1 = selfAdjoint.expUnitary h := by
  apply Subtype.ext
  change NormedSpace.exp (Complex.I • ((1 : ℝ) • (h : H →L[ℂ] H))) = _
  rw [one_smul]
  rfl

private theorem exponentialPath_sub_one_le (h : selfAdjoint (H →L[ℂ] H)) (t : ℝ) :
    ‖(exponentialPath h t : H →L[ℂ] H) - 1‖ ≤ |t| * ‖(h : H →L[ℂ] H)‖ := by
  have hb := norm_expUnitary_sub_expUnitary_le (t • h) 0
  simpa only [selfAdjoint.expUnitary_zero, OneMemClass.coe_one, ZeroMemClass.coe_zero,
    sub_zero, selfAdjoint.val_smul, norm_smul, Real.norm_eq_abs, exponentialPath] using hb

private def exponentialGenerator (h : selfAdjoint (H →L[ℂ] H)) : H →L[ℂ] H :=
  Complex.I • (h : H →L[ℂ] H)

private theorem exponentialGenerator_star (h : selfAdjoint (H →L[ℂ] H)) :
    star (exponentialGenerator h) = -exponentialGenerator h := by
  rw [exponentialGenerator, star_smul, h.property.star_eq]
  change (starRingEnd ℂ) Complex.I • (h : H →L[ℂ] H) = _
  rw [Complex.conj_I, neg_smul]

private theorem exponentialGenerator_norm (h : selfAdjoint (H →L[ℂ] H)) :
    ‖exponentialGenerator h‖ = ‖(h : H →L[ℂ] H)‖ := by
  rw [exponentialGenerator, norm_smul, Complex.norm_I, one_mul]

private def conjugationPath (h : selfAdjoint (H →L[ℂ] H)) (x : H →L[ℂ] H) (t : ℝ) :
    H →L[ℂ] H := unitaryConj (exponentialPath h t) x

private theorem conjugationPath_deriv (h : selfAdjoint (H →L[ℂ] H))
    (x : H →L[ℂ] H) (t : ℝ) :
    HasDerivAt (conjugationPath h x)
      (exponentialGenerator h * conjugationPath h x t -
        conjugationPath h x t * exponentialGenerator h) t := by
  have hd := ((exponentialPath_deriv_left h t).mul_const x).mul
    (exponentialPath_deriv_left h t).star
  convert hd using 1
  · rfl
  · dsimp [conjugationPath, unitaryConj]
    change exponentialGenerator h * ((exponentialPath h t : H →L[ℂ] H) * x *
      star (exponentialPath h t : H →L[ℂ] H)) -
      ((exponentialPath h t : H →L[ℂ] H) * x *
      star (exponentialPath h t : H →L[ℂ] H)) * exponentialGenerator h = _
    change _ = (exponentialGenerator h * (exponentialPath h t : H →L[ℂ] H) * x) *
      star (exponentialPath h t : H →L[ℂ] H) +
      ((exponentialPath h t : H →L[ℂ] H) * x) *
        star (exponentialGenerator h * (exponentialPath h t : H →L[ℂ] H))
    rw [star_mul, exponentialGenerator_star]
    noncomm_ring

private theorem conjugationPath_sub_le (h : selfAdjoint (H →L[ℂ] H))
    (x : H →L[ℂ] H) (t : ℝ) :
    ‖conjugationPath h x t - x‖ ≤ 2 * |t| * ‖(h : H →L[ℂ] H)‖ * ‖x‖ := by
  calc
    _ ≤ 2 * ‖(exponentialPath h t : H →L[ℂ] H) - 1‖ * ‖x‖ :=
      norm_unitaryConj_sub_le _ _
    _ ≤ 2 * (|t| * ‖(h : H →L[ℂ] H)‖) * ‖x‖ := by
      gcongr
      exact exponentialPath_sub_one_le h t
    _ = _ := by ring

private def conjugationRemainder (h : selfAdjoint (H →L[ℂ] H))
    (x : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H :=
  conjugationPath h x t - x -
    t • (exponentialGenerator h * x - x * exponentialGenerator h)

private def conjugationRemainderDerivative (h : selfAdjoint (H →L[ℂ] H))
    (x : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H :=
  exponentialGenerator h * (conjugationPath h x t - x) -
    (conjugationPath h x t - x) * exponentialGenerator h

private theorem conjugationRemainder_deriv (h : selfAdjoint (H →L[ℂ] H))
    (x : H →L[ℂ] H) (t : ℝ) :
    HasDerivAt (conjugationRemainder h x) (conjugationRemainderDerivative h x t) t := by
  have hd := ((conjugationPath_deriv h x t).sub_const x).sub
    ((hasDerivAt_id t).smul_const (exponentialGenerator h * x - x * exponentialGenerator h))
  convert hd using 1
  · rfl
  · dsimp [conjugationRemainderDerivative]
    simp only [one_smul]
    noncomm_ring

private theorem conjugationRemainderDerivative_norm_le (h : selfAdjoint (H →L[ℂ] H))
    (x : H →L[ℂ] H) (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    ‖conjugationRemainderDerivative h x t‖ ≤ 4 * ‖(h : H →L[ℂ] H)‖ ^ 2 * ‖x‖ := by
  have habs : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2.le
  calc
    _ ≤ ‖exponentialGenerator h‖ * ‖conjugationPath h x t - x‖ +
      ‖conjugationPath h x t - x‖ * ‖exponentialGenerator h‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    _ = 2 * ‖(h : H →L[ℂ] H)‖ * ‖conjugationPath h x t - x‖ := by
      rw [exponentialGenerator_norm]; ring
    _ ≤ 2 * ‖(h : H →L[ℂ] H)‖ * (2 * |t| * ‖(h : H →L[ℂ] H)‖ * ‖x‖) := by
      gcongr
      exact conjugationPath_sub_le h x t
    _ ≤ 2 * ‖(h : H →L[ℂ] H)‖ * (2 * 1 * ‖(h : H →L[ℂ] H)‖ * ‖x‖) := by gcongr
    _ = _ := by ring

/-- The first-order conjugation formula with a uniform quadratic remainder. -/
private theorem conjugationRemainder_norm_le
    (h : selfAdjoint (H →L[ℂ] H)) (x : H →L[ℂ] H) :
    ‖conjugationRemainder h x 1‖ ≤
        4 * ‖(h : H →L[ℂ] H)‖ ^ 2 * ‖x‖ := by
  have hb := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (conjugationRemainder_deriv h x t).hasDerivWithinAt)
    (conjugationRemainderDerivative_norm_le h x)
  simpa only [conjugationRemainder, conjugationPath, exponentialPath_zero,
    unitaryConj_one, zero_smul, sub_self, sub_zero] using hb

/-- First-order conjugation by an exponential, with a quadratic norm remainder. -/
theorem norm_expUnitary_conjugation_remainder_le
    (h : selfAdjoint (H →L[ℂ] H)) (x : H →L[ℂ] H) :
    ‖unitaryConj (H := H) (selfAdjoint.expUnitary h) x - x -
      (Complex.I • ((h : H →L[ℂ] H) * x - x * (h : H →L[ℂ] H)) : H →L[ℂ] H)‖ ≤
        4 * ‖(h : H →L[ℂ] H)‖ ^ 2 * ‖x‖ := by
  simpa only [conjugationRemainder, conjugationPath, exponentialPath_one,
    one_smul, exponentialGenerator, smul_sub, smul_mul_assoc, mul_smul_comm]
    using conjugationRemainder_norm_le h x

end

end KadisonKastler

end OAI
