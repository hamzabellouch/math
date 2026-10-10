import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Recursion.EuclideanFarKernelOccupiedIntegrable

namespace OAI

/-! Quantitative estimates for the distance-set construction. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Set MeasureTheory Filter Real Attempt4FarGrid
open scoped ContDiff ComplexConjugate Topology ENNReal
attribute [local instance] Classical.propDecidable

theorem euclidean_source_comparable_far_rapidND {n : ℕ} {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : ∀ t, Ψ t≠0 → t∈Ioo (1/4:ℝ) 4) (C : ℝ) (hC : 0≤C)
    {σ : ℝ} (hσ : 0<σ) (hσ₁ : σ≤1) (err T D : ℝ) (ell : ℕ)
    (hK : 32*(n+2:ℝ)≤(2:ℝ)^ell) :
    ∃ J : ℕ, ∃ H : ℝ, 0≤H ∧ ∀ᶠ R : ℝ in atTop,
      ∀ (N : ℕ), 0<N → R=(2:ℝ)^N →
      ∀ (ρ κ : Measure (EuclideanSpace ℝ (Fin (n+1)))), ∀ [IsFiniteMeasure ρ] [IsFiniteMeasure κ],
      ∀ (a L h : ℕ) (X Y : Fin (n+1) → ℤ)
        (v ma : ℝ) (mb : ℕ → ℝ)
        (b c : (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) → EuclideanSpace ℝ (Fin (n+1)) → ℂ)
        (U W : (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) → Set (EuclideanSpace ℝ (Fin (n+1)))),
      ∀ S : Set ((EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) ×
        (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1)))),
      MeasurableSet S → S⊆farComparableSetND a h X Y → v-a≤N →
      ((h+ell+2:ℕ):ℝ)≤v-2*(max L (Nat.ceil (10*σ*N)):ℕ)+D →
      (∀ k∈Finset.Icc (a+1) (h+ell+2), ∀ i∈occupiedDescendantsND ρ a k X,
        R^(-mb k-err)≤(ρ (ambientGridCell k i)).toReal) →
      (∀ k∈Finset.Icc (a+1) (h+ell+2), ∀ j∈occupiedDescendantsND κ a k Y,
        R^(-mb k-err)≤(κ (ambientGridCell k j)).toReal) →
      (ρ (ambientGridCell a X)).toReal≤R^(-ma+err) →
      (κ (ambientGridCell a Y)).toReal≤R^(-ma+err) →
      Measurable (Function.uncurry b) → Measurable (Function.uncurry c) →
      MeasurableSet {x | euclideanPairDirectionND x∈U x} →
      MeasurableSet {x | euclideanPairDirectionND x∈W x} →
      (∀ k∈Finset.Icc (a+1) (h+ell+2), ∀ p∈occupiedFarPairsND ρ a k ((2:ℝ)^ell) X,
        ∀ᵐ x ∂gridPairMeasureND ρ k p,
          ContDiff ℝ ∞ (b x) ∧
          (∀ w∈U x, -w∈U x) ∧ tsupport (b x) ⊆ U x ∧
          (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j (b x) w‖≤C*(shellEffectiveScaleND L R σ)^j)) →
      (∀ k∈Finset.Icc (a+1) (h+ell+2), ∀ q∈occupiedFarPairsND κ a k ((2:ℝ)^ell) Y,
        ∀ᵐ x ∂gridPairMeasureND κ k q,
          ContDiff ℝ ∞ (c x) ∧
          (∀ w∈W x, -w∈W x) ∧ tsupport (c x) ⊆ W x ∧
          (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j (c x) w‖≤C*(shellEffectiveScaleND L R σ)^j)) →
      ((2:ℝ)^((n+1:ℝ)*(v-a))/(R^(-ma))^4)*
        ‖∫ x in S, euclideanFarKernelND Ψ v b c x ∂(ρ.prod ρ).prod (κ.prod κ)‖ ≤
        H*(∑ k∈Finset.Icc (a+1) (h+ell+2),
          R^(-2*((mb k-(n+1:ℝ)*k/(2*N))-(ma-(n+1:ℝ)*a/(2*N)))+4*err)*
            (farChildMaximumND ρ κ k (occupiedFarPairsND ρ a k ((2:ℝ)^ell) X)
              (occupiedFarPairsND κ a k ((2:ℝ)^ell) Y) v (R^(-mb k)) U W).toReal)+
          R^(-T) := by
  obtain ⟨J,H,hH,hh⟩ := euclidean_source_comparable_far_branchND hΨ hs C hC hσ hσ₁ err (T+1) D ell hK
  refine ⟨J,H,hH,?_⟩
  filter_upwards [hh,far_depth_error_eventuallyND D T] with R hh herror
  intro N hN hRN ρ κ _ _ a L h X Y v ma mb b c U W S hS hSG hav hdepth
    hl₁ hl₂ hu₁ hu₂ hmb hmc hU hW hb hc
  have hmain := hh N hN hRN ρ κ a L h X Y v ma mb b c U W S hS hSG hav hdepth
    hl₁ hl₂ hu₁ hu₂ hmb hmc hU hW hb hc
  have hu : ((h+ell+2:ℕ):ℝ)≤v+D := by
    have he : (0:ℝ)≤(max L (Nat.ceil (10*σ*N)):ℕ) := Nat.cast_nonneg _
    linarith
  exact hmain.trans (add_le_add le_rfl (herror N a (h+ell+2) v hRN hu hav))

end Attempt4FullFar
end GraphLiteralSupport
end
end

end OAI
