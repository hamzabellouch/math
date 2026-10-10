import OAI.MeasureTheory.Falconer.Angular.SphereProduct

namespace OAI

/-! # Measurable frequency parameters in the exact spherical expressions -/

namespace Falconer
open MeasureTheory

theorem sphereOscillation_frequency_measurable {d : ℕ} (e : Sphere d)
    (B : Sphere d → ℂ) (hB : Measurable B) :
    Measurable (fun r : ℝ => sphereOscillation r e B) := by
  have h : Measurable (fun z : ℝ × Sphere d =>
      Complex.exp (Complex.I*(z.1:ℂ)*
        (inner ℝ (z.2:Space d) (e:Space d):ℂ))*B z.2) := by
    fun_prop
  exact h.stronglyMeasurable.integral_prod_right'.measurable

theorem stationarySphereApprox_frequency_measurable (m J : ℕ)
    (B : Space (m+3) → ℂ) (e : Sphere (m+3)) :
    Measurable (fun r : ℝ => stationarySphereApprox m J r B e) := by
  unfold stationarySphereApprox directStationarySum
  fun_prop

end Falconer

end OAI
