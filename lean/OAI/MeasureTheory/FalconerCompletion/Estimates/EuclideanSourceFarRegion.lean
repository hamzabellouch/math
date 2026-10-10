import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Estimates.EuclideanFarNormalizedRegion
import OAI.MeasureTheory.FalconerCompletion.Recursion.FarDepthRegimeEventually

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

theorem euclidean_source_far_regionND {n : ℕ} {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : ∀ t, Ψ t≠0 → t∈Ioo (1/4:ℝ) 4) (C : ℝ) (hC : 0≤C)
    {σ : ℝ} (hσ : 0<σ) (hσ₁ : σ≤1) (err T K D : ℝ) (hK : 32*(n+2:ℝ)≤K) :
    ∃ J : ℕ, ∃ H : ℝ, 0≤H ∧ ∀ᶠ R : ℝ in atTop,
      ∀ (N : ℕ), 0<N → R=(2:ℝ)^N →
      ∀ (ρ κ : Measure (EuclideanSpace ℝ (Fin (n+1)))), ∀ [IsFiniteMeasure ρ] [IsFiniteMeasure κ],
      ∀ (a : ℝ) (L k : ℕ) (P Q : Finset ((Fin (n+1) → ℤ) × (Fin (n+1) → ℤ)))
        (L₁ L₂ : Finset (Fin (n+1) → ℤ)) (X Y : Set (EuclideanSpace ℝ (Fin (n+1))))
        (v ma mb : ℝ) (b c : (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) → EuclideanSpace ℝ (Fin (n+1)) → ℂ)
        (U W : (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) → Set (EuclideanSpace ℝ (Fin (n+1)))),
      v-a≤N → a≤k → (k:ℝ)≤v-2*(max L (Nat.ceil (10*σ*N)):ℕ)+D →
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
        (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j (b x) w‖≤C*(shellEffectiveScaleND L R σ)^j)) →
      (∀ q∈Q, ∀ᵐ x ∂gridPairMeasureND κ k q,
        ContDiff ℝ ∞ (c x) ∧
        (∀ w∈W x, -w∈W x) ∧ tsupport (c x) ⊆ W x ∧
        (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j (c x) w‖≤C*(shellEffectiveScaleND L R σ)^j)) →
      ((2:ℝ)^((n+1:ℝ)*(v-a))/(R^(-ma))^4)*
        ‖∫ x in (⋃ pq∈P.product Q, gridPairSetND k pq.1 ×ˢ gridPairSetND k pq.2),
          euclideanFarKernelND Ψ v b c x ∂(ρ.prod ρ).prod (κ.prod κ)‖ ≤
        H*R^(-2*((mb-(n+1:ℝ)*k/(2*N))-(ma-(n+1:ℝ)*a/(2*N)))+4*err)*
          (farChildMaximumND ρ κ k P Q v (R^(-mb)) U W).toReal+R^(-T) := by
  obtain ⟨J,H,hH,hh⟩ := euclidean_far_normalized_regionND (n := n) hΨ hs C hC hσ err T K hK
  refine ⟨J,H,hH,?_⟩
  filter_upwards [hh,far_source_point_regime_eventuallyND hσ hσ₁ D] with R hh hpoint
  intro N hN hRN ρ κ _ _ a L k P Q L₁ L₂ X Y v ma mb b c U W hav hak hdepth hPx hQy
    hL₁ hL₂ hP hQ hs₁ hs₂ hl₁ hl₂ hu₁ hu₂ hmb hmc hU hW hb hc
  have hK' : 32*((n+1:ℕ)+1:ℝ)≤K := by push_cast; linarith
  let A := shellEffectiveScaleND L R σ
  have hreg := hpoint N L k a v ((2:ℝ)^(-(k:ℝ))/4) hRN hak hav hdepth le_rfl
  have hbl : ∀ p∈P, ∀ᵐ x ∂gridPairMeasureND ρ k p,
      ContDiff ℝ ∞ (b x) ∧ (∀ w∈U x, -w∈U x) ∧ tsupport (b x) ⊆ U x ∧
      A^2/((2:ℝ)^v*dist x.1 x.2)≤R^(-σ) ∧
      (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j (b x) w‖≤C*A^j) := by
    intro p hp
    filter_upwards [farSeparatedGridND_ae_lower hK' ρ p (hP p hp),hb p hp] with x hx hb
    exact ⟨hb.1,hb.2.1,hb.2.2.1,(hpoint N L k a v (dist x.1 x.2) hRN hak hav hdepth hx).2.2.2,hb.2.2.2⟩
  have hcl : ∀ q∈Q, ∀ᵐ x ∂gridPairMeasureND κ k q,
      ContDiff ℝ ∞ (c x) ∧ (∀ w∈W x, -w∈W x) ∧ tsupport (c x) ⊆ W x ∧
      A^2/((2:ℝ)^v*dist x.1 x.2)≤R^(-σ) ∧
      (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j (c x) w‖≤C*A^j) := by
    intro q hq
    filter_upwards [farSeparatedGridND_ae_lower hK' κ q (hQ q hq),hc q hq] with x hx hc
    exact ⟨hc.1,hc.2.1,hc.2.2.1,(hpoint N L k a v (dist x.1 x.2) hRN hak hav hdepth hx).2.2.2,hc.2.2.2⟩
  exact hh N hN hRN ρ κ a k P Q L₁ L₂ X Y v ma mb A b c U W hav hreg.1 hreg.2.1 hPx hQy
    hL₁ hL₂ hP hQ hs₁ hs₂ hl₁ hl₂ hu₁ hu₂ hmb hmc hU hW hbl hcl

end Attempt4FullFar
end GraphLiteralSupport
end
end

end OAI
