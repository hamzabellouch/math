import Mathlib
import OAI.Geometry.Cannon.Energy.MeshEnergy

namespace OAI

section
section
section
noncomputable section
section
section
section
namespace CannonApprox

open CannonMagnification CannonCrossEnergy Set Metric Filter Topology MeasureTheory

structure RecordData {X Γ : Type*} [MetricSpace X] [MeasurableSpace X]
    (action : Γ → X ≃ₜ X) (ι : ℕ → Type*) [∀ n, Fintype (ι n)]
    (p : ∀ n, ι n → X) (r : ℕ → ℝ) where
  Ω : Set X
  isOpen : IsOpen Ω
  f : X → ℝ
  continuous : ContinuousOn f Ω
  unit : ∀ x ∈ Ω, f x ∈ Icc (0:ℝ) 1
  x₀ : X
  x₀mem : x₀ ∈ Ω
  variation : ∀ s : ℝ, 0 < s → ∃ y ∈ ball x₀ s, f y ≠ f x₀
  z₀ : X
  z₀not : z₀ ∉ Ω
  ν : FiniteMeasure X
  E : ℝ
  E_nonneg : 0 ≤ E
  Cμ : ℝ
  Cμ_pos : 0 < Cμ
  measure_bound : ∀ K : Set X, IsCompact K → K ⊆ Ω → ∃ s₀ : ℝ, 0 < s₀ ∧
    ∀ s : ℝ, 0 < s → s ≤ s₀ → ∀ x ∈ K,
      closedBall x s ⊆ Ω ∧ (CannonCrossEnergy.oscillation f (closedBall x s))^2 ≤
        E*(ν (closedBall x (Cμ*s)) : ℝ)
  level : ℝ → Set X
  diameter : ℝ
  diameter_pos : 0 < diameter
  level_properties : ∀ t ∈ Ioo (0:ℝ) 1,
    IsCompact (level t) ∧ IsConnected (level t) ∧ diameter ≤ diam (level t) ∧
      ∀ y ∈ level t, y ∈ Ω → f y=t
  level_hits : ∀ t ∈ Ioo (0:ℝ) 1, ∀ u v, ∀ γ : Path u v, range γ ⊆ Ω →
    f u < t → t < f v → (level t ∩ range γ).Nonempty
  H : ℕ → X → ℝ
  H_unit : ∀ n x, H n x ∈ Icc (0:ℝ) 1
  H_continuous : ∀ n, ContinuousOn (H n) Ω
  H_limit : ∀ K : Set X, IsCompact K → K ⊆ Ω → TendstoUniformlyOn H f atTop K
  H_diameter : ℝ
  H_diameter_pos : 0 < H_diameter
  H_level : ∀ n t, t ∈ Ioo (0:ℝ) 1 → ∃ K : Set X,
    IsCompact K ∧ IsConnected K ∧ H_diameter ≤ diam K ∧ (∀ y ∈ K, H n y=t) ∧
    ∀ u v, ∀ γ : Path u v, range γ ⊆ Ω → H n u < t → t < H n v →
      (K ∩ range γ).Nonempty
  energy : ∀ g : Γ, ∀ K : Set X, IsCompact K → K ⊆ action g '' Ω →
    ∀ J : ℝ, 0 < J → Tendsto (fun n => meshEnergy (p n) (r n) J
      (H n ∘ (action g).symm) K) atTop (𝓝 0)

end CannonApprox

end
end
end
end
end
end
end

end OAI
