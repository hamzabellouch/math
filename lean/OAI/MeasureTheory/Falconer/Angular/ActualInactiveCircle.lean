import OAI.MeasureTheory.Falconer.Angular.RotatedActualInactive
import OAI.MeasureTheory.Falconer.Angular.RotatedConeKernel
import OAI.MeasureTheory.Falconer.Fourier.InheritedSymbolMeasurability

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

theorem uniform_actual_inactive_circle_kernel
    {sig κ c T outer : ℝ} (hsig : 0 < sig) (hgap : 10*sig < κ) (hc : 0 < c)
    (K₁ K₂ : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (L : ℕ) (t u r : ℝ),
    κ*(N : ℝ) ≤ t → t ≤ u+2*sig*(N : ℝ) → 10*sig*(N : ℝ) ≤ u →
    (L : ℝ) ≤ u+2*sig*(N : ℝ) →
    ∀ (e : UnitCircle) (φ axis : ℝ), |φ| ≤ 1/20 →
    dist (sourceUnitDirection φ) e ≤ graphUncappedAngularScale N sig t →
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
    x-y = ‖x-y‖ • sourceDirection (φ+axis) → c*(2 : ℝ)^(t+u) ≤ r*‖x-y‖ →
    ((2 : ℝ)^N)^outer * ‖sourceDistanceKernel
      (fun dir => sourceConeCircle axis dir *
        rotatedBinSelection (angularBinCount (graphUncappedAngularScale N sig t))
          (inactiveAngularLabels (angularBinCount (graphUncappedAngularScale N sig t)) e
            (3*graphUncappedAngularScale N sig t)) axis dir)
      (inheritedCircleSymbol S₁ b₁ k₁ Q₁ ρ₁ m₁ N lam₁ sig J₁ i₁ h₁)
      (inheritedCircleSymbol S₂ b₂ k₂ Q₂ ρ₂ m₂ N lam₂ sig J₂ i₂ h₂) r x y‖ ≤ ((2 : ℝ)^N)^(-T) := by
  obtain ⟨N₀, hN₀⟩ := uniform_rotated_actual_inactive_bins (T := T) (outer := outer)
    graphConeCutoff_contDiff (by norm_num : (-1/5 : ℝ) ≤ 1/5)
    graphConeCutoff_support hsig hgap hc K₁ K₂
  refine ⟨N₀, ?_⟩
  intro N hN L t u r hlow ht hu hL e φ axis hφ hmove ι₁ ι₂ inst₁ inst₂
    S₁ b₁ k₁ S₂ b₂ k₂ hc₁ hk₁ hc₂ hk₂ hl₁ hl₂ Q₁ Q₂ hQ₁ hQ₂
    ρ₁ ρ₂ m₁ m₂ lam₁ lam₂ J₁ i₁ J₂ i₂ hsp₁ hsp₂ x y hm₁ hm₂ hx hy hΔ hΛ
  rw [sourceDistanceKernel_rotated_bins axis r φ _ _ _ _ x y
    ((measurable_inheritedCircleSymbol S₁ b₁ k₁ Q₁ ρ₁ m₁ N lam₁ sig J₁ i₁ hsp₁ hm₁).comp
      (measurable_const.prodMk measurable_id))
    ((measurable_inheritedCircleSymbol S₂ b₂ k₂ Q₂ ρ₂ m₂ N lam₂ sig J₂ i₂ hsp₂ hm₂).comp
      (measurable_const.prodMk measurable_id)) hΔ]
  exact hN₀ N hN L t u (r*‖x-y‖) hlow ht hu hL hΛ e φ axis
    (hφ.trans (by have := Real.one_le_pi_div_two; linarith)) hmove
    (graphConeCutoff_forward hφ) S₁ b₁ k₁ S₂ b₂ k₂ hc₁ hk₁ hc₂ hk₂ hl₁ hl₂
    Q₁ Q₂ hQ₁ hQ₂ ρ₁ ρ₂ m₁ m₂ lam₁ lam₂ J₁ i₁ J₂ i₂ hsp₁ hsp₂ x y hx hy

end PlanarFalconer

end OAI
