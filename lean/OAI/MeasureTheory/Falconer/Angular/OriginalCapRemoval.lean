import OAI.MeasureTheory.Falconer.Angular.OriginalFiberCaps

namespace OAI

/-! # The prepared cap deletion controls both original sphere laws -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem original_cap_removal (μ ν : ProbabilityMeasure (Space d))
    (Γ : ℕ → Set (Space d × Space d)) (hcap : CapAvailable μ ν Γ ((d:ℝ)/2))
    (hne : ∀ N, ∀ z ∈ Γ N, z.1 ≠ z.2) {σ : ℝ} (hσ : 0 < σ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∃ D : Set (Space d × Space d), MeasurableSet D ∧ D ⊆ Γ N ∧
        ((μ : Measure (Space d)).prod (ν : Measure (Space d))) D ≤
          ENNReal.ofReal (C*((2:ℝ)^N)^(-c)) ∧
        ∀ w₀ : Sphere d,
        (∀ᵐ x ∂(μ : Measure (Space d)), ∀ u : Space d, ∀ r : ℝ,
          ((2:ℝ)^N)^(-1:ℝ) ≤ r → r ≤ 1 →
          originalRadialSphereLaw w₀ ν (Γ N \ D) x {w : Sphere d | dist (w:Space d) u < r} ≤
            ENNReal.ofReal (((2:ℝ)^N)^σ*r^((d:ℝ)/2))) ∧
        (∀ᵐ y ∂(ν : Measure (Space d)), ∀ u : Space d, ∀ r : ℝ,
          ((2:ℝ)^N)^(-1:ℝ) ≤ r → r ≤ 1 →
          originalRadialSphereLaw w₀ μ (Prod.swap ⁻¹' (Γ N \ D)) y
            {w : Sphere d | dist (w:Space d) u < r} ≤
            ENNReal.ofReal (((2:ℝ)^N)^σ*r^((d:ℝ)/2))) := by
  obtain ⟨c,C,hc,hC,N₁,h₁⟩ := hcap (σ/2) (half_pos hσ)
  obtain ⟨N₂,h₂⟩ := eventual_original_fiber_caps (d := d) hσ (show (0:ℝ) ≤ d/2 by positivity)
  refine ⟨c,C,hc,hC,max N₁ N₂,?_⟩
  intro N hN
  obtain ⟨D,hD,hsub,hm,hcaps⟩ := h₁ N ((le_max_left _ _).trans hN)
  refine ⟨D,hD,hsub,hm,?_⟩
  intro w₀
  constructor
  · filter_upwards [(μ : Measure (Space d)).support_mem_ae] with x hx
    exact h₂ N ((le_max_right _ _).trans hN) μ ν (Γ N \ D)
      (fun x _ y hxy => (hne N (x,y) hxy.1).symm) hcaps.1 w₀ x hx
  · filter_upwards [(ν : Measure (Space d)).support_mem_ae] with y hy
    apply h₂ N ((le_max_right _ _).trans hN) ν μ (Prod.swap ⁻¹' (Γ N \ D))
      (fun y _ x hxy => hne N (x,y) hxy.1) ?_ w₀ y hy
    intro y hy u hu r hr hr1
    exact hcaps.2 y hy u hu r hr hr1

end Falconer

end OAI
