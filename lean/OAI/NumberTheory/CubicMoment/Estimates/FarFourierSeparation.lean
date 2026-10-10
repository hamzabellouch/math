import OAI.NumberTheory.CubicMoment.Estimates.FarHeightIntegration
import OAI.NumberTheory.CubicMoment.Estimates.HeightMeanSquare

namespace OAI

/-! Exact Fourier separation of the far product cutoff. The kernel has
uniform L1 norm, and its shifts act on the actual norm twists. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators FourierTransform
namespace CubicFirstMoment

def farFourierKernel (J u : ℝ) : ℂ :=
  𝓕 (fun x : ℝ => farInverseSquare (J*x)) u

lemma farFourierKernel_integrable {J : ℝ} (hJ : 0 < J) :
    Integrable (farFourierKernel J) := far_dilated_fourier_integrable hJ

lemma farFourierKernel_mass {J : ℝ} (hJ : 0 < J) :
    (∫ u : ℝ, ‖farFourierKernel J u‖) = ∫ u : ℝ, ‖𝓕 farInverseSquare u‖ :=
  farInverseSquare_fourier_dilation hJ

lemma farFourierKernel_phase_integrable {J : ℝ} (hJ : 0 < J) (x : ℝ) :
    Integrable (fun u : ℝ => farFourierKernel J u *
      Complex.exp ((2*Real.pi*u*x:ℝ)*Complex.I)) := by
  apply (farFourierKernel_integrable hJ).mul_bdd (c := 1)
  · exact (by fun_prop : Continuous (fun u : ℝ =>
      Complex.exp ((2*Real.pi*u*x:ℝ)*Complex.I))).aestronglyMeasurable
  · exact Eventually.of_forall (fun u => by simp [Complex.norm_exp])

lemma far_finite_fourier_separation {ι : Type*} (S : Finset ι)
    (c : ι → ℂ) (x : ι → ℝ) {J : ℝ} (hJ : 0 < J) :
    (∑ a ∈ S, c a*farInverseSquare (J*x a)) =
      ∫ u : ℝ, farFourierKernel J u *
        ∑ a ∈ S, c a*Complex.exp ((2*Real.pi*u*x a:ℝ)*Complex.I) := by
  calc
    _ = ∑ a ∈ S, ∫ u : ℝ, c a*(farFourierKernel J u*
        Complex.exp ((2*Real.pi*u*x a:ℝ)*Complex.I)) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [integral_const_mul,far_fourier_representation hJ]
      congr 1
      apply integral_congr_ae
      filter_upwards with u
      exact mul_comm _ _
    _ = ∫ u : ℝ, ∑ a ∈ S, c a*(farFourierKernel J u*
        Complex.exp ((2*Real.pi*u*x a:ℝ)*Complex.I)) :=
      (integral_finsetSum S (fun a _ =>
        (farFourierKernel_phase_integrable hJ (x a)).const_mul (c a))).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with u
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ => by ring)

lemma normTwist_far_phase (s u x₀ : ℝ) (a : Eisenstein) :
    normTwist s a * Complex.exp ((2*Real.pi*u*(Real.log (norm a)-x₀):ℝ)*Complex.I) =
      Complex.exp ((-2*Real.pi*u*x₀:ℝ)*Complex.I) * normTwist (s+2*Real.pi*u) a := by
  unfold normTwist
  rw [←Complex.exp_add,←Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The finite Gauss sum with the far cutoff is an integral of the
original polynomial at common shifted heights. -/
theorem far_norm_sum_separation {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (n : ι → Eisenstein) (s x₀ : ℝ) {J : ℝ} (hJ : 0 < J) :
    (∑ a ∈ S, c a*normTwist s (n a)*
      farInverseSquare (J*(Real.log (norm (n a))-x₀))) =
      ∫ u : ℝ, farFourierKernel J u *
        Complex.exp ((-2*Real.pi*u*x₀:ℝ)*Complex.I) *
          ∑ a ∈ S, c a*normTwist (s+2*Real.pi*u) (n a) := by
  rw [far_finite_fourier_separation S (fun a => c a*normTwist s (n a))
    (fun a => Real.log (norm (n a))-x₀) hJ]
  apply integral_congr_ae
  filter_upwards with u
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  calc
    _ = farFourierKernel J u * (c a * (normTwist s (n a) *
        Complex.exp ((2*Real.pi*u*(Real.log (norm (n a))-x₀):ℝ)*Complex.I))) := by ring
    _ = _ := by rw [normTwist_far_phase]; ring

theorem far_gauss_sum_separation (S : Finset Eisenstein) (c : Eisenstein → ℂ)
    (s x₀ : ℝ) {J : ℝ} (hJ : 0 < J) :
    (∑ a ∈ S, c a*normTwist s a*
      farInverseSquare (J*(Real.log (norm a)-x₀))) =
      ∫ u : ℝ, farFourierKernel J u *
        Complex.exp ((-2*Real.pi*u*x₀:ℝ)*Complex.I) *
          ∑ a ∈ S, c a*normTwist (s+2*Real.pi*u) a :=
  far_norm_sum_separation S c id s x₀ hJ

end CubicFirstMoment

end

end OAI
