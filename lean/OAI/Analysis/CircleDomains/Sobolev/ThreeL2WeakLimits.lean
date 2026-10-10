import OAI.Analysis.CircleDomains.Sobolev.L2WeakSubsequence

namespace OAI

/-! A common weakly convergent subsequence for one scalar and its two
differential components, allowing the scalar measure to be spherical. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem exists_three_L2_weak_limits
    {X : Type*} [MeasurableSpace X] (μ₀ μ₁ μ₂ : Measure X)
    [IsSeparable μ₀] [IsSeparable μ₁] [IsSeparable μ₂]
    (u₀ u₁ u₂ : ℕ → X → ℝ)
    (h₀ : ∀ n, MemLp (u₀ n) 2 μ₀) (h₁ : ∀ n, MemLp (u₁ n) 2 μ₁)
    (h₂ : ∀ n, MemLp (u₂ n) 2 μ₂) (C₀ C₁ C₂ : ℝ)
    (hb₀ : ∀ n, ‖(h₀ n).toLp (u₀ n)‖ ≤ C₀)
    (hb₁ : ∀ n, ‖(h₁ n).toLp (u₁ n)‖ ≤ C₁)
    (hb₂ : ∀ n, ‖(h₂ n).toLp (u₂ n)‖ ≤ C₂) :
    ∃ (V : Lp ℝ 2 μ₀) (G₁ : Lp ℝ 2 μ₁) (G₂ : Lp ℝ 2 μ₂)
      (σ : ℕ → ℕ), StrictMono σ ∧
      (∀ w : Lp ℝ 2 μ₀, Tendsto (fun n => ∫ x, u₀ (σ n) x * w x ∂μ₀)
        atTop (𝓝 (∫ x, V x * w x ∂μ₀))) ∧
      (∀ w : Lp ℝ 2 μ₁, Tendsto (fun n => ∫ x, u₁ (σ n) x * w x ∂μ₁)
        atTop (𝓝 (∫ x, G₁ x * w x ∂μ₁))) ∧
      (∀ w : Lp ℝ 2 μ₂, Tendsto (fun n => ∫ x, u₂ (σ n) x * w x ∂μ₂)
        atTop (𝓝 (∫ x, G₂ x * w x ∂μ₂))) := by
  obtain ⟨V, _, s₀, hs₀, hv⟩ := exists_L2_weak_subsequence μ₀ u₀ h₀ C₀ hb₀
  obtain ⟨G₁, _, s₁, hs₁, hg₁⟩ := exists_L2_weak_subsequence μ₁ (u₁ ∘ s₀)
    (fun n => h₁ (s₀ n)) C₁ (fun n => hb₁ (s₀ n))
  obtain ⟨G₂, _, s₂, hs₂, hg₂⟩ := exists_L2_weak_subsequence μ₂ (u₂ ∘ s₀ ∘ s₁)
    (fun n => h₂ (s₀ (s₁ n))) C₂ (fun n => hb₂ (s₀ (s₁ n)))
  refine ⟨V, G₁, G₂, s₀ ∘ s₁ ∘ s₂, hs₀.comp (hs₁.comp hs₂), ?_, ?_, ?_⟩
  · intro w
    exact (hv w).comp (hs₁.tendsto_atTop.comp hs₂.tendsto_atTop)
  · intro w
    exact (hg₁ w).comp hs₂.tendsto_atTop
  · exact hg₂

end CircleDomainRigidity

end

end OAI
