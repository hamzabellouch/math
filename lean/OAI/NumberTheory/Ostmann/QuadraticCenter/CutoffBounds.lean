import OAI.NumberTheory.Ostmann.QuadraticCenter.InverseWeylPhase
import OAI.NumberTheory.Ostmann.SchwartzCutoff

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped SchwartzMap FourierTransform

def cutoffFourier : SchwartzMap ℝ ℂ := 𝓕 SchwartzCutoff.psi

theorem cutoffSeminorm_nonneg (n : ℕ) :
    0 ≤ SchwartzMap.seminorm ℂ 0 n cutoffFourier := by
  have h := cutoffFourier.le_seminorm' ℂ 0 n 0
  simp only [pow_zero, one_mul] at h
  exact (norm_nonneg _).trans h

def cutoffFourierBound : ℝ :=
  SchwartzMap.seminorm ℂ 0 0 (cutoffFourier) +
    SchwartzMap.seminorm ℂ 0 1 (cutoffFourier) + 1

theorem cutoffFourierBound_pos : 0 < cutoffFourierBound := by
  have h0 := cutoffSeminorm_nonneg 0
  have h1 := cutoffSeminorm_nonneg 1
  unfold cutoffFourierBound
  linarith

theorem norm_cutoff_fourier_le (x : ℝ) : ‖cutoffFourier x‖ ≤ cutoffFourierBound := by
  have h := (cutoffFourier).le_seminorm' ℂ 0 0 x
  have h1 := cutoffSeminorm_nonneg 1
  simp only [pow_zero, one_mul, iteratedDeriv_zero] at h
  unfold cutoffFourierBound
  linarith

theorem norm_deriv_cutoff_fourier_le (x : ℝ) :
    ‖deriv (cutoffFourier) x‖ ≤ cutoffFourierBound := by
  have h := (cutoffFourier).le_seminorm' ℂ 0 1 x
  have h0 := cutoffSeminorm_nonneg 0
  simp only [pow_zero, one_mul, iteratedDeriv_one] at h
  unfold cutoffFourierBound
  linarith

theorem cutoff_fourier_lipschitz (x y : ℝ) :
    ‖cutoffFourier x - cutoffFourier y‖ ≤ cutoffFourierBound * |x - y| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := Set.univ) (f := (cutoffFourier : ℝ → ℂ))
    (fun z _ => (cutoffFourier).differentiableAt)
    (fun z _ => norm_deriv_cutoff_fourier_le z) (convex_univ : Convex ℝ (Set.univ : Set ℝ))
    (Set.mem_univ y) (Set.mem_univ x)
  simpa only [Real.norm_eq_abs] using h

theorem weylPhase_lipschitz (x y : ℝ) :
    ‖weylPhase x - weylPhase y‖ ≤ (2 * Real.pi) * |x - y| := by
  have heq : weylPhase x - weylPhase y = (weylPhase (x - y) - 1) * weylPhase y := by
    rw [sub_mul, one_mul, ← weylPhase_add]
    congr 1
    ring_nf
  rw [heq, norm_mul, weylPhase_norm, mul_one]
  have he : weylPhase (x - y) = Complex.exp (Complex.I * (2 * Real.pi * (x - y) : ℝ)) := by
    rw [weylPhase, Real.fourierChar_apply, mul_comm]
  rw [he]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * (x - y))
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using h

end Ostmann.QuadraticCenter

end

end OAI
