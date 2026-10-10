import OAI.NumberTheory.CubicMoment.Estimates.CubeLattice

namespace OAI

/-! The cubic pullback of the radial Fourier transform is a Schwartz function. -/

noncomputable section
open scoped SchwartzMap ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

private lemma cube_norm_growth :
    ∃ (k : ℕ) (C : ℝ), ∀ z : ℂ, ‖z‖ ≤ C*(1+‖z^3‖)^k := by
  refine ⟨1,1,?_⟩
  intro z
  simp only [one_mul,pow_one,norm_pow]
  by_cases hz : ‖z‖ ≤ 1
  · nlinarith [pow_nonneg (_root_.norm_nonneg z) 3]
  · have hh : 1 ≤ ‖z‖ := le_of_lt (lt_of_not_ge hz)
    have hp := mul_nonneg (mul_nonneg (_root_.norm_nonneg z) (sub_nonneg.mpr hh))
      (by positivity : 0 ≤ ‖z‖+1)
    nlinarith

def cubeProfileSchwartz (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) : 𝓢(ℂ,ℂ) :=
  SchwartzMap.compCLM ℂ (by fun_prop : (fun z : ℂ => z^3).HasTemperateGrowth)
    cube_norm_growth (normProfileFourierSchwartz W hW hW')

lemma cubeProfileSchwartz_apply (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) (z : ℂ) :
    cubeProfileSchwartz W hW hW' z = radialDualProfile W ((Complex.normSq z)^3) := by
  change normProfileFourierSchwartz W hW hW' (z^3) = _
  rw [normProfileFourierSchwartz_apply,normProfileFourier_radial,map_pow]

lemma cubeProfileSchwartz_scaled_apply (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) (s : ℝ) (j : Eisenstein) :
    cubeProfileSchwartz W hW hW' ((s:ℂ)*(j:ℂ)) =
      radialDualProfile W ((s^2)^3*(norm j)^3) := by
  rw [cubeProfileSchwartz_apply,Complex.normSq_mul,Complex.normSq_ofReal,mul_pow]
  simp only [← pow_two]
  rfl

end CubicFirstMoment

end

end OAI
