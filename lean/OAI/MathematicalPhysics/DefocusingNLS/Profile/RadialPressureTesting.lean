import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialStepTesting
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPressureStepConvergence

namespace OAI

/-! The proved pressure-primitive limit yields its expected C1 test integrals. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS

theorem radial_pressure_amplitude_test_convergence (R l b : ℝ) (hl : 0 ≤ l) (hlR : l ≤ R)
    (p : ℕ → ℕ) (H : ℕ → ℝ → ℝ) (hH : ∀ n, Continuous (H n))
    (hT : TendstoUniformlyOn (fun n r => ∫ t in (0 : ℝ)..r, (H n t)^(p n)*t^11)
      (fun r => b/12*(min r l)^12) atTop (Icc 0 R))
    (φ ψ : ℝ → ℝ) (hφ : Continuous φ) (hψ : Continuous ψ)
    (hφD : ∀ r ∈ Ioo 0 R, HasDerivAt φ (ψ r) r) :
    Tendsto (fun n => ∫ t in (0 : ℝ)..R, (H n t)^(p n)*φ t*t^11) atTop
      (𝓝 (b*∫ t in (0 : ℝ)..l, φ t*t^11)) := by
  have hh := radial_primitive_test_convergence R (hl.trans hlR)
    (fun n t => (H n t)^(p n)*t^11)
    (fun n => ((hH n).pow (p n)).mul (continuous_id.pow 11))
    (fun r => b/12*(min r l)^12) (by fun_prop) hT φ ψ hφ hψ hφD
  rw [radial_step_test_identity R l b hl hlR φ ψ hφ hψ hφD] at hh
  have hlim : (∫ t in (0 : ℝ)..l, φ t*(b*t^11))=b*∫ t in (0 : ℝ)..l, φ t*t^11 := by
    calc
      _ = ∫ t in (0 : ℝ)..l, b*(φ t*t^11) := by
        apply intervalIntegral.integral_congr
        intro t _
        ring
      _ = _ := intervalIntegral.integral_const_mul _ _
  rw [hlim] at hh
  apply hh.congr'
  exact Eventually.of_forall (fun n => by
    apply intervalIntegral.integral_congr
    intro t _
    ring)

end DefocusingNLS

end OAI
