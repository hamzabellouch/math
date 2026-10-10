import OAI.Analysis.KadisonKastler.StripContourLimit
import OAI.Analysis.KadisonKastler.StripContourBoundary
import OAI.Analysis.KadisonKastler.StripKernelMass

namespace OAI

/-! # The scalar modular strip averaging formula

This is the contour identity of Rieffel--Van Daele, Lemma 4.6, for the
centered strip. The pole is removed before applying rectangle integration.
-/

namespace KadisonKastler

open MeasureTheory Set

noncomputable section

theorem centered_strip_average (φ : ℝ) (hφ : |φ| < Real.pi) (f : ℂ → ℂ)
    (hc : ContinuousOn f {z : ℂ | |z.re| ≤ 1 / 2})
    (hd : DifferentiableOn ℂ f {z : ℂ | |z.re| < 1 / 2})
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ z : ℂ, |z.re| ≤ 1 / 2 → ‖f z‖ ≤ B) :
    (∫ t : ℝ, stripAverageKernel Real.pi (φ : ℂ) t *
      (Complex.exp (Complex.I * φ / 2) * f ((1 / 2 : ℂ) + t * Complex.I) +
        Complex.exp (-(Complex.I * φ / 2)) * f ((-1 / 2 : ℂ) + t * Complex.I))) = f 0 := by
  let kp := stripAverageKernel Real.pi (φ : ℂ)
  let k0 := stripAverageKernel Real.pi 0
  have hk : Integrable kp := stripAverageKernel_integrable (by simpa using hφ)
  have hk0 : Integrable k0 := stripAverageKernel_integrable (by simpa using Real.pi_pos)
  have hi (x : ℝ) (hx : |x| ≤ 1 / 2) :
      Integrable (fun t : ℝ => kp t * f ((x : ℂ) + t * Complex.I)) := by
    have hc' : Continuous (fun t : ℝ => f ((x : ℂ) + t * Complex.I)) :=
      hc.comp_continuous (by fun_prop) (fun t => by simpa using hx)
    exact hk.mul_bdd hc'.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun t => hb _ (by simpa using hx)))
  let p : ℝ → ℂ := fun t => kp t *
    (Complex.exp (Complex.I * φ / 2) * f ((1 / 2 : ℂ) + t * Complex.I))
  let m : ℝ → ℂ := fun t => kp t *
    (Complex.exp (-(Complex.I * φ / 2)) * f ((-1 / 2 : ℂ) + t * Complex.I))
  have hp : Integrable p := by
    convert! (hi (1 / 2) (by norm_num)).const_mul (Complex.exp (Complex.I * φ / 2)) using 1
    funext t
    dsimp [p]
    push_cast
    ring
  have hm : Integrable m := by
    convert! (hi (-1 / 2) (by norm_num)).const_mul (Complex.exp (-(Complex.I * φ / 2))) using 1
    funext t
    dsimp [m]
    push_cast
    ring
  have hrfun : (fun t : ℝ => stripSineQuotient φ f ((1 / 2 : ℂ) + t * Complex.I)) =
      fun t => 2 * p t - (2 * f 0) * k0 t := by
    funext t
    rw [stripSineQuotient_right]
    dsimp [p, kp, k0]
    ring
  have hlfun : (fun t : ℝ => stripSineQuotient φ f ((-1 / 2 : ℂ) + t * Complex.I)) =
      fun t => (-2) * m t + (2 * f 0) * k0 t := by
    funext t
    rw [stripSineQuotient_left]
    dsimp [m, kp, k0]
    ring
  have hr : Integrable (fun t : ℝ => stripSineQuotient φ f ((1 / 2 : ℂ) + t * Complex.I)) := by
    rw [hrfun]
    exact (hp.const_mul 2).sub (hk0.const_mul (2 * f 0))
  have hl : Integrable (fun t : ℝ => stripSineQuotient φ f ((-1 / 2 : ℂ) + t * Complex.I)) := by
    rw [hlfun]
    exact (hm.const_mul (-2)).add (hk0.const_mul (2 * f 0))
  have he := stripSineQuotient_integral_edges_eq φ hφ f hc hd B hB hb hr hl
  rw [hrfun, hlfun, integral_sub (hp.const_mul 2) (hk0.const_mul (2 * f 0)),
    integral_add (hm.const_mul (-2)) (hk0.const_mul (2 * f 0))] at he
  simp only [integral_const_mul] at he
  change 2 * (∫ t, p t) - 2 * f 0 * (∫ t, stripAverageKernel Real.pi 0 t) =
    (-2) * (∫ t, m t) + 2 * f 0 * (∫ t, stripAverageKernel Real.pi 0 t) at he
  rw [integral_stripAverageKernel_zero] at he
  have hsum : (∫ t, p t) + (∫ t, m t) = f 0 := by linear_combination (1 / 2 : ℂ) * he
  rw [← integral_add hp hm] at hsum
  convert hsum using 1
  congr 1
  funext t
  dsimp [p, m, kp]
  ring

end

end KadisonKastler

end OAI
