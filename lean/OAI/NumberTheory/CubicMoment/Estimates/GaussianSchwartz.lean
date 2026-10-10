import OAI.NumberTheory.CubicMoment.Estimates.GaussianRapidDecay

namespace OAI

/-! The actual radial Gaussian as a Schwartz test function for lattice Poisson. -/
noncomputable section
open scoped SchwartzMap
namespace CubicFirstMoment

def radialGaussianSchwartzReal (a : ℝ) (ha : 0 < a) : 𝓢(ℂ,ℝ) where
  toFun := radialGaussian a
  smooth' := radialGaussian_smooth a
  decay' k n := by
    obtain ⟨P,hP,he⟩ := radialGaussian_derivative_factor a n
    obtain ⟨d,C,hC,hb⟩ := hP.norm_iteratedFDeriv_le_uniform 0
    obtain ⟨B,hB,hdecay⟩ := gaussian_polynomial_bound ha k d
    refine ⟨C*B,?_⟩
    intro z
    have hPz : ‖P z‖ ≤ C*(1+‖z‖)^d := by simpa only [norm_iteratedFDeriv_zero] using hb 0 le_rfl z
    rw [he,norm_smul]
    have hn : ‖radialGaussian a z‖ = Real.exp (-a*‖z‖^2) :=
      Real.norm_of_nonneg (Real.exp_pos _).le
    rw [hn]
    calc
      _ ≤ ‖z‖^k*(Real.exp (-a*‖z‖^2)*(C*(1+‖z‖)^d)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hPz (Real.exp_pos _).le) (by positivity)
      _ = C*(‖z‖^k*(1+‖z‖)^d*Real.exp (-a*‖z‖^2)) := by ring
      _ ≤ C*B := mul_le_mul_of_nonneg_left (hdecay ‖z‖ (_root_.norm_nonneg z)) hC

def radialGaussianSchwartz (a : ℝ) (ha : 0 < a) : 𝓢(ℂ,ℂ) :=
  (radialGaussianSchwartzReal a ha).postcompCLM Complex.ofRealCLM

@[simp] lemma radialGaussianSchwartz_apply (a : ℝ) (ha : 0 < a) (z : ℂ) :
    radialGaussianSchwartz a ha z = (Real.exp (-a*‖z‖^2):ℝ) := rfl

lemma radialGaussianSchwartz_traceFourier (a : ℝ) (ha : 0 < a) (w : ℂ) :
    traceFourier (radialGaussianSchwartz a ha) w =
      (Real.pi/a:ℝ) * (Real.exp (-4*Real.pi^2/a*Complex.normSq w):ℝ) := by
  have he : (radialGaussianSchwartz a ha : ℂ → ℂ) =
      fun z => Complex.exp (-(a:ℂ)*‖z‖^2) := by
    funext z
    rw [radialGaussianSchwartz_apply,Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [he,traceFourier_gaussian ha]
  rw [Complex.ofReal_exp]

end CubicFirstMoment

end

end OAI
