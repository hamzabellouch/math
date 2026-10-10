import OAI.MeasureTheory.Falconer.Angular.FourPointCaps

namespace OAI

/-! # Interchanging the two independent angular variables

This allows the same nonstationary estimate to remove a failed perpendicular
test at either endpoint, with the original spatial law unchanged.
-/

namespace Falconer
open MeasureTheory

theorem expandedCapTerm_swap {d : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (v : ℝ) (Ψ : ℝ → ℝ) (v₁ v₂ : X → Space d)
    (b₁ b₂ : X → Sphere d → ℂ) :
    expandedCapTerm μ v Ψ v₁ v₂ b₁ b₂ = expandedCapTerm μ v Ψ v₂ v₁ b₂ b₁ := by
  unfold expandedCapTerm
  apply integral_congr_ae
  filter_upwards with r
  rw [← integral_prod_swap]
  apply integral_congr_ae
  filter_upwards with z
  apply integral_congr_ae
  filter_upwards with x
  dsimp only [Prod.swap]
  rw [add_comm (inner ℝ (z.2 : Space d) (v₁ x) : ℂ)]
  ring


theorem endpointCapCrossTerm_swap {d : ℕ}
    (μ μ' ν ν' : Measure (Space d)) (M M' P P' v : ℝ) (Ψ : ℝ → ℝ)
    (b b' c c' : Space d → Sphere d → ℂ) (η θ : Sphere d → ℝ) :
    endpointCapCrossTerm μ μ' ν ν' M M' P P' v Ψ b b' c c' η θ =
      endpointCapCrossTerm ν ν' μ μ' P P' M M' v Ψ c c' b b' θ η := by
  unfold endpointCapCrossTerm
  apply integral_congr_ae
  filter_upwards with r
  rw [← integral_prod_swap]
  apply integral_congr_ae
  filter_upwards with z
  dsimp only [Prod.swap]
  simp only [star_mul]
  ring

end Falconer

end OAI
