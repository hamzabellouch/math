import OAI.NumberTheory.CubicMoment.Estimates.FarFourierSeparation

namespace OAI

/-! Angular-frequency normalization of the far-cutoff Fourier kernel.
It has exactly the same L1 mass for every positive cell scale. -/
noncomputable section
open MeasureTheory Filter
open scoped FourierTransform
namespace CubicFirstMoment

def farMellinKernel (J v : ℝ) : ℂ :=
  ((2*Real.pi:ℝ):ℂ)⁻¹*farFourierKernel J (v/(2*Real.pi))

lemma farFourierKernel_continuous {J : ℝ} (hJ : 0 < J) :
    Continuous (farFourierKernel J) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ (far_dilated_integrable hJ)

lemma farMellinKernel_continuous {J : ℝ} (hJ : 0 < J) :
    Continuous (farMellinKernel J) :=
  continuous_const.mul ((farFourierKernel_continuous hJ).comp
    (continuous_id.div_const _))

lemma farMellinKernel_integrable {J : ℝ} (hJ : 0 < J) :
    Integrable (farMellinKernel J) :=
  ((farFourierKernel_integrable hJ).comp_div (by positivity)).const_mul _

lemma farMellinKernel_mass {J : ℝ} (hJ : 0 < J) :
    (∫ v : ℝ, ‖farMellinKernel J v‖) = ∫ u : ℝ, ‖𝓕 farInverseSquare u‖ := by
  simp only [farMellinKernel,norm_mul,norm_inv,Complex.norm_real,
    Real.norm_of_nonneg (show (0:ℝ) ≤ 2*Real.pi by positivity)]
  rw [integral_const_mul]
  have hs := Measure.integral_comp_div (fun v : ℝ => ‖farFourierKernel J v‖) (2*Real.pi)
  rw [hs,abs_of_pos (by positivity : (0:ℝ) < 2*Real.pi),smul_eq_mul]
  rw [inv_mul_cancel_left₀ (by positivity : (2*Real.pi:ℝ) ≠ 0)]
  exact farFourierKernel_mass hJ

/-- Reparametrization to the convention `exp(i*v*log n)` used by `normTwist`. -/
lemma farMellinKernel_reparametrize (J : ℝ) (g : ℝ → ℂ) :
    (∫ v : ℝ, farMellinKernel J v*g v) =
      ∫ u : ℝ, farFourierKernel J u*g (2*Real.pi*u) := by
  let f := fun u : ℝ => farFourierKernel J u*g (2*Real.pi*u)
  have he : (fun v : ℝ => farMellinKernel J v*g v) =
      fun v : ℝ => ((2*Real.pi:ℝ):ℂ)⁻¹*f (v/(2*Real.pi)) := by
    funext v
    dsimp [farMellinKernel,f]
    have hv : 2*Real.pi*(v/(2*Real.pi)) = v := by field_simp
    rw [hv]
    ring
  rw [he,integral_const_mul,Measure.integral_comp_div,
    abs_of_pos (by positivity : (0:ℝ) < 2*Real.pi),Complex.real_smul]
  rw [inv_mul_cancel_left₀ (by exact_mod_cast (show (2*Real.pi:ℝ) ≠ 0 by positivity))]

theorem far_norm_sum_mellin {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (n : ι → Eisenstein) (s x₀ : ℝ) {J : ℝ} (hJ : 0 < J) :
    (∑ a ∈ S, c a*normTwist s (n a)*
      farInverseSquare (J*(Real.log (norm (n a))-x₀))) =
      ∫ v : ℝ, farMellinKernel J v * Complex.exp ((-v*x₀:ℝ)*Complex.I) *
        ∑ a ∈ S, c a*normTwist (s+v) (n a) := by
  rw [far_norm_sum_separation S c n s x₀ hJ]
  have he := farMellinKernel_reparametrize J (fun v =>
    Complex.exp ((-v*x₀:ℝ)*Complex.I) * ∑ a ∈ S, c a*normTwist (s+v) (n a))
  calc
    _ = ∫ u : ℝ, farFourierKernel J u *
        (Complex.exp ((-(2*Real.pi*u)*x₀:ℝ)*Complex.I) *
          ∑ a ∈ S, c a*normTwist (s+2*Real.pi*u) (n a)) := by
      apply integral_congr_ae
      filter_upwards with u
      have hp : (-2*Real.pi*u*x₀:ℝ) = -(2*Real.pi*u)*x₀ := by ring
      rw [hp]
      ring
    _ = _ := he.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with v
      ring

theorem far_gauss_sum_mellin (S : Finset Eisenstein) (c : Eisenstein → ℂ)
    (s x₀ : ℝ) {J : ℝ} (hJ : 0 < J) :
    (∑ a ∈ S, c a*normTwist s a*
      farInverseSquare (J*(Real.log (norm a)-x₀))) =
      ∫ v : ℝ, farMellinKernel J v * Complex.exp ((-v*x₀:ℝ)*Complex.I) *
        ∑ a ∈ S, c a*normTwist (s+v) a :=
  far_norm_sum_mellin S c id s x₀ hJ

end CubicFirstMoment

end

end OAI
