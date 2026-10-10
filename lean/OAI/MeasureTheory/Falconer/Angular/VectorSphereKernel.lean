import OAI.MeasureTheory.Falconer.Angular.AngularPair
import OAI.MeasureTheory.Falconer.Angular.SphereFrequency
import OAI.MeasureTheory.Falconer.Angular.SphereNormalization

namespace OAI

/-! # The original displacement phase in normalized spherical coordinates -/

namespace Falconer
open MeasureTheory

theorem norm_smul_normalizeToSphere {d : ℕ} (w₀ : Sphere d) (v : Space d) :
    ‖v‖ • (normalizeToSphere w₀ v : Space d) = v := by
  by_cases hv : v = 0
  · simp only [hv, norm_zero, zero_smul]
  · rw [normalizeToSphere_coe_of_ne w₀ hv]
    exact NormedSpace.norm_smul_normalize v

theorem sphereOscillator_normalized {d : ℕ} (w₀ : Sphere d)
    (r : ℝ) (v : Space d) (w : Sphere d) :
    sphereOscillator r v w =
      Complex.exp (Complex.I*((r*‖v‖):ℂ)*
        (inner ℝ (w:Space d) (normalizeToSphere w₀ v:Space d):ℂ)) := by
  have hi : inner ℝ (w:Space d) v =
      ‖v‖*inner ℝ (w:Space d) (normalizeToSphere w₀ v:Space d) := by
    nth_rw 1 [← norm_smul_normalizeToSphere w₀ v]
    rw [inner_smul_right]
  rw [sphereOscillator, hi]
  push_cast
  congr 1
  ring

theorem vectorSphereIntegral_eq_oscillation {d : ℕ} (w₀ : Sphere d)
    (r : ℝ) (v : Space d) (B : Sphere d → ℂ) :
    (∫ w, sphereOscillator r v w*B w ∂sphereMeasure d) =
      sphereOscillation (r*‖v‖) (normalizeToSphere w₀ v) B := by
  apply integral_congr_ae
  filter_upwards with w
  rw [sphereOscillator_normalized w₀]
  simp only [Complex.ofReal_mul]

end Falconer

end OAI
