import OAI.Analysis.KadisonKastler.ComplexLocalLaplace
import OAI.Analysis.KadisonKastler.GaussianStateKernel

namespace OAI

/-! # Gaussian translates separate bounded continuous coefficients -/

namespace KadisonKastler

open MeasureTheory Set

noncomputable section

theorem gaussianStateKernel_tilt (r : ℝ) (hr : 0 < r) (s t : ℝ) :
    (Real.exp (s * t) : ℂ) * gaussianStateKernel r 0 t =
      (Real.exp (s ^ 2 / (4 * r)) : ℂ) * gaussianStateKernel r (s / (2 * r) : ℝ) t := by
  rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) from rfl, gaussianStateKernel_real,
    gaussianStateKernel_real, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  have hne : r ≠ 0 := hr.ne'
  field_simp
  ring

theorem zero_of_gaussian_averages (r : ℝ) (hr : 0 < r) (g : ℝ → ℂ)
    (hg : Continuous g) (B : ℝ) (hB : ∀ t, ‖g t‖ ≤ B)
    (hz : ∀ s : ℝ, (∫ t : ℝ, gaussianStateKernel r s t * g t) = 0) : g = 0 := by
  let f : ℝ → ℂ := fun t => gaussianStateKernel r 0 t * g t
  have hc : Continuous f := by
    apply Continuous.mul _ hg
    unfold gaussianStateKernel
    fun_prop
  have he (s : ℝ) :
      (fun t => (Real.exp (s * t) : ℂ) * f t) =
        fun t => (Real.exp (s ^ 2 / (4 * r)) : ℂ) *
          (gaussianStateKernel r (s / (2 * r) : ℝ) t * g t) := by
    funext t
    dsimp [f]
    rw [← mul_assoc, gaussianStateKernel_tilt r hr, mul_assoc]
  have hi (s : ℝ) : Integrable (fun t => (Real.exp (s * t) : ℂ) * f t) := by
    rw [he]
    exact ((gaussianStateKernel_integrable hr (s / (2 * r) : ℝ)).mul_bdd
      hg.aestronglyMeasurable (Filter.Eventually.of_forall hB)).const_mul _
  have hf : f = 0 := zero_of_complex_local_laplace f hc (a := 1) zero_lt_one
    (fun s _ => hi s) (fun s _ => by rw [he, integral_const_mul, hz, mul_zero])
  funext t
  have h := congrFun hf t
  change gaussianStateKernel r 0 t * g t = 0 at h
  exact (mul_eq_zero.mp h).resolve_left (Complex.exp_ne_zero _)

end

end KadisonKastler

end OAI
