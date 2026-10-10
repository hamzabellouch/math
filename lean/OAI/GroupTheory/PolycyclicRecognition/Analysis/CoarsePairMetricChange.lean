import OAI.GroupTheory.PolycyclicRecognition.Analysis.CompatibleMetricComparison

namespace OAI

/-! # Uniform coarse-pair estimates under a change of compatible metric -/

noncomputable section
namespace PolycyclicRecognition

theorem coarse_pair_metric_change
    {G P : Type} [Group G] [TopologicalSpace G]
    (d₁ d₂ : ProperChainMetric G) {κ ξ ε : ℝ}
    (hκ : 0 ≤ κ) (hξ : 0 ≤ ξ) (hε : 0 ≤ ε)
    (f g : P → G → G)
    (hf : letI := d₁.compatibleMetric
      ∀ p x y, dist (f p x) (f p y) ≤ κ * dist x y + ξ)
    (hg : letI := d₁.compatibleMetric
      ∀ p x y, dist (g p x) (g p y) ≤ κ * dist x y + ξ)
    (hgf : letI := d₁.compatibleMetric; ∀ p x, dist (g p (f p x)) x ≤ ε)
    (hfg : letI := d₁.compatibleMetric; ∀ p x, dist (f p (g p x)) x ≤ ε) :
    letI := d₂.compatibleMetric
    ∃ κ' ξ' ε' : ℝ, 0 ≤ κ' ∧ 0 ≤ ξ' ∧ 0 ≤ ε' ∧
      (∀ p x y, dist (f p x) (f p y) ≤ κ' * dist x y + ξ') ∧
      (∀ p x y, dist (g p x) (g p y) ≤ κ' * dist x y + ξ') ∧
      (∀ p x, dist (g p (f p x)) x ≤ ε') ∧
      (∀ p x, dist (f p (g p x)) x ≤ ε') := by
  obtain ⟨a, b, ha, hb, h₁₂⟩ := d₁.compare d₂
  obtain ⟨a', b', ha', hb', h₂₁⟩ := d₂.compare d₁
  let := d₂.compatibleMetric
  let oldDist := @dist G d₁.compatibleMetric.toPseudoMetricSpace.toDist
  have hcontrol (F : P → G → G)
      (hF : ∀ p x y, oldDist (F p x) (F p y) ≤ κ * oldDist x y + ξ) :
      ∀ p x y, dist (F p x) (F p y) ≤
        (a * κ * a') * dist x y + (a * κ * b' + a * ξ + b) := by
    intro p x y
    calc
      _ ≤ a * oldDist (F p x) (F p y) + b := h₁₂ _ _
      _ ≤ a * (κ * oldDist x y + ξ) + b := by gcongr; exact hF p x y
      _ ≤ a * (κ * (a' * dist x y + b') + ξ) + b := by gcongr; exact h₂₁ x y
      _ = _ := by ring
  refine ⟨a * κ * a', a * κ * b' + a * ξ + b, a * ε + b,
    by positivity, by positivity, by positivity, hcontrol f hf, hcontrol g hg, ?_, ?_⟩
  · intro p x
    exact (h₁₂ _ _).trans (add_le_add (mul_le_mul_of_nonneg_left (hgf p x) ha) le_rfl)
  · intro p x
    exact (h₁₂ _ _).trans (add_le_add (mul_le_mul_of_nonneg_left (hfg p x) ha) le_rfl)

end PolycyclicRecognition

end

end OAI
