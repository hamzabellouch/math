import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Estimates.EuclideanFarKernelRegionPartition

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

theorem euclidean_far_normalized_regionND {n : ℕ} {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : ∀ t, Ψ t≠0 → t∈Ioo (1/4:ℝ) 4) (C : ℝ) (hC : 0≤C)
    {θ : ℝ} (hθ : 0<θ) (err T K : ℝ) (hK : 32*(n+2:ℝ)≤K) :
    ∃ J : ℕ, ∃ H : ℝ, 0≤H ∧ ∀ᶠ R : ℝ in atTop,
      ∀ (N : ℕ), 0<N → R=(2:ℝ)^N →
      ∀ (ρ κ : Measure (EuclideanSpace ℝ (Fin (n+1)))), ∀ [IsFiniteMeasure ρ] [IsFiniteMeasure κ],
      ∀ (a : ℝ) (k : ℕ) (P Q : Finset ((Fin (n+1) → ℤ) × (Fin (n+1) → ℤ)))
        (L₁ L₂ : Finset (Fin (n+1) → ℤ)) (X Y : Set (EuclideanSpace ℝ (Fin (n+1))))
        (v ma mb A : ℝ) (b c : (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) → EuclideanSpace ℝ (Fin (n+1)) → ℂ)
        (U W : (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) → Set (EuclideanSpace ℝ (Fin (n+1)))),
      v-a≤N → 1≤A → A≤R^2 →
      (∀ p∈P, ambientGridCell k p.1⊆X ∧ ambientGridCell k p.2⊆X) →
      (∀ q∈Q, ambientGridCell k q.1⊆Y ∧ ambientGridCell k q.2⊆Y) →
      (∀ p∈P, p.1∈L₁) → (∀ q∈Q, q.1∈L₂) →
      (∀ p∈P, farSeparatedGridND k K p.1 p.2) → (∀ q∈Q, farSeparatedGridND k K q.1 q.2) →
      (∀ i∈L₁, ambientGridCell k i⊆X) → (∀ j∈L₂, ambientGridCell k j⊆Y) →
      (∀ i∈L₁, R^(-mb-err)≤(ρ (ambientGridCell k i)).toReal) →
      (∀ j∈L₂, R^(-mb-err)≤(κ (ambientGridCell k j)).toReal) →
      (ρ X).toReal≤R^(-ma+err) → (κ Y).toReal≤R^(-ma+err) →
      Measurable (Function.uncurry b) → Measurable (Function.uncurry c) →
      MeasurableSet {x | euclideanPairDirectionND x∈U x} →
      MeasurableSet {x | euclideanPairDirectionND x∈W x} →
      (∀ p∈P, ∀ᵐ x ∂gridPairMeasureND ρ k p,
        ContDiff ℝ ∞ (b x) ∧
        (∀ w∈U x, -w∈U x) ∧ tsupport (b x) ⊆ U x ∧
        A^2/((2:ℝ)^v*dist x.1 x.2)≤R^(-θ) ∧
        (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j (b x) w‖≤C*A^j)) →
      (∀ q∈Q, ∀ᵐ x ∂gridPairMeasureND κ k q,
        ContDiff ℝ ∞ (c x) ∧
        (∀ w∈W x, -w∈W x) ∧ tsupport (c x) ⊆ W x ∧
        A^2/((2:ℝ)^v*dist x.1 x.2)≤R^(-θ) ∧
        (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j (c x) w‖≤C*A^j)) →
      ((2:ℝ)^((n+1:ℝ)*(v-a))/(R^(-ma))^4)*
        ‖∫ x in (⋃ pq∈P.product Q, gridPairSetND k pq.1 ×ˢ gridPairSetND k pq.2),
          euclideanFarKernelND Ψ v b c x ∂(ρ.prod ρ).prod (κ.prod κ)‖ ≤
        H*R^(-2*((mb-(n+1:ℝ)*k/(2*N))-(ma-(n+1:ℝ)*a/(2*N)))+4*err)*
          (farChildMaximumND ρ κ k P Q v (R^(-mb)) U W).toReal+R^(-T) := by
  have hK0 : 0≤K := by have hn : (0:ℝ)≤n := Nat.cast_nonneg n; linarith
  obtain ⟨J,H,hH,hh⟩ := euclidean_far_normalized_sumND (n := n) hΨ hs C hC hθ err T K hK0
  refine ⟨J,H,hH,hh.mono ?_⟩
  intro R hh N hN hRN ρ κ _ _ a k P Q L₁ L₂ X Y v ma mb A b c U W hav hA hAup hPx hQy
    hL₁ hL₂ hP hQ hs₁ hs₂ hl₁ hl₂ hu₁ hu₂ hmb hmc hU hW hb hc
  have hK' : 32*((n+1:ℕ)+1:ℝ)≤K := by push_cast; linarith
  have hbl : ∀ p∈P, ∀ᵐ x ∂gridPairMeasureND ρ k p,
      (2:ℝ)^(-(k:ℝ))/4≤dist x.1 x.2 ∧ ContDiff ℝ ∞ (b x) ∧
        (∀ w∈U x, -w∈U x) ∧ tsupport (b x) ⊆ U x ∧
        A^2/((2:ℝ)^v*dist x.1 x.2)≤R^(-θ) ∧
        (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j (b x) w‖≤C*A^j) := by
    intro p hp
    filter_upwards [farSeparatedGridND_ae_lower hK' ρ p (hP p hp),hb p hp] with x hx hb
    exact ⟨hx,hb⟩
  have hcl : ∀ q∈Q, ∀ᵐ x ∂gridPairMeasureND κ k q,
      (2:ℝ)^(-(k:ℝ))/4≤dist x.1 x.2 ∧ ContDiff ℝ ∞ (c x) ∧
        (∀ w∈W x, -w∈W x) ∧ tsupport (c x) ⊆ W x ∧
        A^2/((2:ℝ)^v*dist x.1 x.2)≤R^(-θ) ∧
        (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j (c x) w‖≤C*A^j) := by
    intro q hq
    filter_upwards [farSeparatedGridND_ae_lower hK' κ q (hQ q hq),hc q hq] with x hx hc
    exact ⟨hx,hc⟩
  have hbd : ∀ p∈P, ∀ᵐ x ∂gridPairMeasureND ρ k p, ∀ w, ‖w‖=1 → ‖b x w‖≤C := by
    intro p hp
    filter_upwards [hb p hp] with x hx
    intro w hw
    simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one] using hx.2.2.2.2 0 (by omega) w hw
  have hcd : ∀ q∈Q, ∀ᵐ x ∂gridPairMeasureND κ k q, ∀ w, ‖w‖=1 → ‖c x w‖≤C := by
    intro q hq
    filter_upwards [hc q hq] with x hx
    intro w hw
    simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one] using hx.2.2.2.2 0 (by omega) w hw
  rw [euclideanFarKernelND_local_partition hΨ.continuous hs v b c hmb hmc ρ κ k P Q hC hbd hcd]
  exact hh N hN hRN ρ κ a k P Q L₁ L₂ X Y v ma mb A b c U W hav hA hAup hPx hQy
    hL₁ hL₂ hP hQ hs₁ hs₂ hl₁ hl₂ hu₁ hu₂ hU hW hbl hcl

end Attempt4FullFar
end GraphLiteralSupport
end
end

end OAI
