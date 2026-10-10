import OAI.MeasureTheory.Falconer.Recursion.ParentCellGeometry
import OAI.MeasureTheory.Falconer.Angular.ActualInactiveCircle

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem uniform_parent_inactive_kernel
    {sig κ T outer : ℝ} (hsig : 0 < sig) (hgap : 10*sig < κ)
    (K₁ K₂ : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (L : ℕ) (a p v r : ℝ),
    κ*(N : ℝ) ≤ p-a → p-a ≤ v-p+2*sig*(N : ℝ) → 10*sig*(N : ℝ) ≤ v-p →
    (L : ℝ) ≤ v-p+2*sig*(N : ℝ) →
    ∀ X Y P Q : DyadicSquare,
    0 < X.side → 0 < Y.side → 0 < P.side → 0 < Q.side →
    X.side ≤ (2:ℝ)^(-a) → Y.side ≤ (2:ℝ)^(-a) →
    P.side ≤ (2:ℝ)^(-p) → Q.side ≤ (2:ℝ)^(-p) →
    P.carrier ⊆ X.carrier → Q.carrier ⊆ Y.carrier →
    100*(2:ℝ)^(-a) ≤ dist X.center Y.center →
    dist X.center Y.center ≤ 2000*(2:ℝ)^(-a) →
    ∀ Ψ : ℝ → ℝ, (∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4 : ℝ) 4) →
    Ψ (r/(2:ℝ)^v) ≠ 0 →
    ∀ {ι₁ ι₂ : Type} [DecidableEq ι₁] [DecidableEq ι₂],
    ∀ (S₁ : Finset ι₁) (b₁ : ι₁ → PolicyDescriptor) (k₁ : ι₁ → ℕ)
      (S₂ : Finset ι₂) (b₂ : ι₂ → PolicyDescriptor) (k₂ : ι₂ → ℕ),
    S₁.card ≤ (N+1)^3+1 → (∑ d ∈ S₁, k₁ d) ≤ K₁ →
    S₂.card ≤ (N+1)^3+1 → (∑ d ∈ S₂, k₂ d) ≤ K₂ →
    (∀ d ∈ S₁, descriptorLength (b₁ d) ≤ L) → (∀ d ∈ S₂, descriptorLength (b₂ d) ≤ L) →
    ∀ Q₁ Q₂ : DyadicSquare, 0 < Q₁.side → 0 < Q₂.side →
    ∀ (ρ₁ ρ₂ : Measure Plane) (m₁ m₂ : ℝ → ℝ) (lam₁ lam₂ : ℝ)
      (J₁ i₁ J₂ i₂ : ℕ) (h₁ h₂ : Plane → ℂ) (x y : Plane),
    Measurable h₁ → Measurable h₂ → ‖h₁ x‖ ≤ 1 → ‖h₂ y‖ ≤ 1 →
    x ∈ P.carrier → y ∈ Q.carrier →
    ((2 : ℝ)^N)^outer * ‖sourceDistanceKernel
      (fun dir => sourceConeCircle (sourceParentAxis X Y) dir *
        rotatedBinSelection (angularBinCount (graphUncappedAngularScale N sig (p-a)))
          (inactiveAngularLabels (angularBinCount (graphUncappedAngularScale N sig (p-a))) (sourceCenteredCellDirection X Y P Q)
            (3*graphUncappedAngularScale N sig (p-a))) (sourceParentAxis X Y) dir)
      (inheritedCircleSymbol S₁ b₁ k₁ Q₁ ρ₁ m₁ N lam₁ sig J₁ i₁ h₁)
      (inheritedCircleSymbol S₂ b₂ k₂ Q₂ ρ₂ m₂ N lam₂ sig J₂ i₂ h₂) r x y‖ ≤ ((2 : ℝ)^N)^(-T) := by
  obtain ⟨N₁,hN₁⟩ := uniform_actual_inactive_circle_kernel (c := 24) (T := T)
    (outer := outer) hsig hgap (by norm_num) K₁ K₂
  obtain ⟨N₂,hN₂⟩ := uniform_parent_cell_geometry_frequency hsig
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN L a p v r hlow ht hu hL X Y P Q hX hY hP hQ hXa hYa hPp hQp hPX hQY hlo hhi
    Ψ hΨ hr ι₁ ι₂ inst₁ inst₂ S₁ b₁ k₁ S₂ b₂ k₂ hc₁ hk₁ hc₂ hk₂ hl₁ hl₂ Q₁ Q₂ hQ₁ hQ₂
    ρ₁ ρ₂ m₁ m₂ lam₁ lam₂ J₁ i₁ J₂ i₂ hsp₁ hsp₂ x y hm₁ hm₂ hx hy hxP hyQ
  obtain ⟨φ,hφ,hmove,hΔ,hΛ,_⟩ := hN₂ N ((le_max_right _ _).trans hN) a p v X Y P Q
    hX hY hP hQ hXa hYa hPp hQp hPX hQY hlo hhi Ψ hΨ r hr x hxP y hyQ
  exact hN₁ N ((le_max_left _ _).trans hN) L (p-a) (v-p) r hlow ht hu hL
    (sourceCenteredCellDirection X Y P Q) φ (sourceParentAxis X Y) hφ hmove
    S₁ b₁ k₁ S₂ b₂ k₂ hc₁ hk₁ hc₂ hk₂ hl₁ hl₂ Q₁ Q₂ hQ₁ hQ₂
    ρ₁ ρ₂ m₁ m₂ lam₁ lam₂ J₁ i₁ J₂ i₂ hsp₁ hsp₂ x y hm₁ hm₂ hx hy hΔ hΛ

end PlanarFalconer

end OAI
