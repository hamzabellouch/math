import OAI.MeasureTheory.Falconer.Angular.FullCircleDecomposition

namespace OAI

namespace PlanarFalconer
open MeasureTheory

 theorem rotated_circle_integral (Λ θ₀ : ℝ) {f : ℝ → ℂ}
    (hp : Function.Periodic f (2*Real.pi)) :
    (∫ θ in (-Real.pi)..Real.pi, cosineOscillator Λ (θ-θ₀)*f θ) =
      ∫ θ in (-Real.pi)..Real.pi, cosineOscillator Λ θ*f (θ+θ₀) := by
  let G : ℝ → ℂ := fun θ => cosineOscillator Λ θ*f (θ+θ₀)
  have hG : Function.Periodic G (2*Real.pi) := by
    intro θ
    have he : θ+2*Real.pi+θ₀ = (θ+θ₀)+2*Real.pi := by ring
    simp only [G,cosineOscillator_periodic Λ θ,he,hp (θ+θ₀)]
  have he : (fun θ => cosineOscillator Λ (θ-θ₀)*f θ) = fun θ => G (θ-θ₀) := by
    funext θ
    simp only [G, sub_add_cancel]
  rw [he,intervalIntegral.integral_comp_sub_right]
  have hh := hG.intervalIntegral_add_eq (-Real.pi-θ₀) (-Real.pi)
  have ha : -Real.pi-θ₀+2*Real.pi = Real.pi-θ₀ := by ring
  have hb : -Real.pi+2*Real.pi = Real.pi := by ring
  simpa only [ha,hb] using hh

end PlanarFalconer

end OAI
