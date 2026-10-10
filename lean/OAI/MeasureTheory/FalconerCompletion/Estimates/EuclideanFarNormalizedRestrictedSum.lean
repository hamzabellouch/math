import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Estimates.EuclideanSourceNoncomparableRegion

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

theorem euclidean_far_normalized_restricted_sumND {n : ℕ} {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : ∀ t, Ψ t≠0 → t∈Ioo (1/4:ℝ) 4) (C : ℝ) (hC : 0≤C)
    {θ : ℝ} (hθ : 0<θ) (err T K : ℝ) (hK : 0≤K) :
    ∃ J : ℕ, ∃ H : ℝ, 0≤H ∧ ∀ᶠ R : ℝ in atTop,
      ∀ (N : ℕ), 0<N → R=(2:ℝ)^N →
      ∀ (ρ κ : Measure (EuclideanSpace ℝ (Fin (n+1)))), ∀ [IsFiniteMeasure ρ] [IsFiniteMeasure κ],
      ∀ (a : ℝ) (k : ℕ) (P Q : Finset ((Fin (n+1) → ℤ) × (Fin (n+1) → ℤ)))
        (L₁ L₂ : Finset (Fin (n+1) → ℤ)) (X Y : Set (EuclideanSpace ℝ (Fin (n+1))))
        (v ma mb A : ℝ) (b c : (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) → EuclideanSpace ℝ (Fin (n+1)) → ℂ)
        (U W : (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) → Set (EuclideanSpace ℝ (Fin (n+1)))),
      ∀ S : Set ((EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) ×
        (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1)))),
      MeasurableSet S → v-a≤N → 1≤A → A≤R^2 →
      (∀ p∈P, ambientGridCell k p.1⊆X ∧ ambientGridCell k p.2⊆X) →
      (∀ q∈Q, ambientGridCell k q.1⊆Y ∧ ambientGridCell k q.2⊆Y) →
      (∀ p∈P, p.1∈L₁) → (∀ q∈Q, q.1∈L₂) →
      (∀ p∈P, farSeparatedGridND k K p.1 p.2) → (∀ q∈Q, farSeparatedGridND k K q.1 q.2) →
      (∀ i∈L₁, ambientGridCell k i⊆X) → (∀ j∈L₂, ambientGridCell k j⊆Y) →
      (∀ i∈L₁, R^(-mb-err)≤(ρ (ambientGridCell k i)).toReal) →
      (∀ j∈L₂, R^(-mb-err)≤(κ (ambientGridCell k j)).toReal) →
      (ρ X).toReal≤R^(-ma+err) → (κ Y).toReal≤R^(-ma+err) →
      MeasurableSet {x | euclideanPairDirectionND x∈U x} →
      MeasurableSet {x | euclideanPairDirectionND x∈W x} →
      (∀ p∈P, ∀ᵐ x ∂gridPairMeasureND ρ k p,
        (2:ℝ)^(-(k:ℝ))/4≤dist x.1 x.2 ∧ ContDiff ℝ ∞ (b x) ∧
        (∀ w∈U x, -w∈U x) ∧ tsupport (b x) ⊆ U x ∧
        A^2/((2:ℝ)^v*dist x.1 x.2)≤R^(-θ) ∧
        (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j (b x) w‖≤C*A^j)) →
      (∀ q∈Q, ∀ᵐ x ∂gridPairMeasureND κ k q,
        (2:ℝ)^(-(k:ℝ))/4≤dist x.1 x.2 ∧ ContDiff ℝ ∞ (c x) ∧
        (∀ w∈W x, -w∈W x) ∧ tsupport (c x) ⊆ W x ∧
        A^2/((2:ℝ)^v*dist x.1 x.2)≤R^(-θ) ∧
        (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j (c x) w‖≤C*A^j)) →
      ((2:ℝ)^((n+1:ℝ)*(v-a))/(R^(-ma))^4)*
        ‖∑ pq∈P.product Q, ∫ x, euclideanFarKernelND Ψ v b c x
          ∂((gridPairMeasureND ρ k pq.1).prod (gridPairMeasureND κ k pq.2)).restrict S‖ ≤
        H*R^(-2*((mb-(n+1:ℝ)*k/(2*N))-(ma-(n+1:ℝ)*a/(2*N)))+4*err)*
          (farChildMaximumND ρ κ k P Q v (R^(-mb)) U W).toReal+R^(-T) := by
  obtain ⟨J,H,hH,hh⟩ := euclidean_far_restricted_sumND (n := n) hΨ hs C hC hθ 0 (T+(n+1:ℝ)+4*err)
  refine ⟨J,H*binKernelConstant.toReal*(8*K+5)^(2*(n+1)),by positivity,?_⟩
  filter_upwards [hh,eventually_gt_atTop (0:ℝ)] with R hh hR
  intro N hN hRN ρ κ _ _ a k P Q L₁ L₂ X Y v ma mb A b c U W S hS hav hA hAup hPx hQy
    hL₁ hL₂ hP hQ hs₁ hs₂ hl₁ hl₂ hu₁ hu₂ hU hW hb hc
  have hsum := hh ρ κ k P Q X Y v (R^(-mb)) A b c U W S hS
    (by positivity) hA hAup hPx hQy hU hW hb hc
  simp only [Real.rpow_zero,one_mul] at hsum
  have hlabel := far_actual_label_normalizationND N hN a k v ma mb err hK
    ρ κ P Q L₁ L₂ X Y hL₁ hL₂ hP hQ hs₁ hs₂
    (by simpa only [← hRN] using hl₁) (by simpa only [← hRN] using hl₂)
    (by simpa only [← hRN] using hu₁) (by simpa only [← hRN] using hu₂)
  dsimp only at hlabel
  simp only [← hRN,Nat.cast_add,Nat.cast_one,add_sub_cancel_right] at hlabel
  have hmass := far_actual_error_normalizationND N hN hav ρ κ X Y
    (by simpa only [← hRN] using hu₁) (by simpa only [← hRN] using hu₂)
  simp only [← hRN,Nat.cast_add,Nat.cast_one] at hmass
  let F := (2:ℝ)^((n+1:ℝ)*(v-a))/(R^(-ma))^4
  let D := (farChildMaximumND ρ κ k P Q v (R^(-mb)) U W).toReal
  have hF : 0≤F := by dsimp [F]; positivity
  have hD : 0≤D := ENNReal.toReal_nonneg
  have he : (F*(ρ X).toReal^2*(κ Y).toReal^2)*R^(-(T+(n+1:ℝ)+4*err))≤R^(-T) := by
    calc
      _ ≤ R^((n+1:ℝ)+4*err)*R^(-(T+(n+1:ℝ)+4*err)) :=
        mul_le_mul_of_nonneg_right hmass (by positivity)
      _ = _ := by rw [← Real.rpow_add hR]; congr 1; ring
  calc
    _ ≤ F*((H*(2:ℝ)^(-(n:ℝ)*(v-k)))*
        (binKernelConstant.toReal*((R^(-mb))^4*(2:ℝ)^(-(v-k)))*((P.product Q).card:ℝ)*D)+
        (ρ X).toReal^2*(κ Y).toReal^2*R^(-(T+(n+1:ℝ)+4*err))) :=
      mul_le_mul_of_nonneg_left hsum hF
    _ = (H*binKernelConstant.toReal*D)*
        (F*(2:ℝ)^(-(n:ℝ)*(v-k))*(R^(-mb))^4*(2:ℝ)^(-(v-k))*((P.product Q).card:ℝ))+
        (F*(ρ X).toReal^2*(κ Y).toReal^2)*R^(-(T+(n+1:ℝ)+4*err)) := by ring
    _ ≤ (H*binKernelConstant.toReal*D)*
        ((8*K+5)^(2*(n+1))*R^(-2*((mb-(n+1:ℝ)*k/(2*N))-(ma-(n+1:ℝ)*a/(2*N)))+4*err))+R^(-T) :=
      add_le_add (mul_le_mul_of_nonneg_left hlabel (by positivity)) he
    _ = _ := by dsimp [D]; ring

end Attempt4FullFar
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Set MeasureTheory
open scoped ContDiff

theorem euclideanFarKernelND_restricted_partition {n : ℕ} {Ψ : ℝ → ℝ} (hΨ : Continuous Ψ)
    (hs : ∀ t, Ψ t≠0 → t∈Ioo (1/4:ℝ) 4) (v : ℝ)
    (b c : (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) → EuclideanSpace ℝ (Fin (n+1)) → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    (ρ κ : Measure (EuclideanSpace ℝ (Fin (n+1)))) [IsFiniteMeasure ρ] [IsFiniteMeasure κ]
    (a : ℕ) (P Q : Finset ((Fin (n+1) → ℤ) × (Fin (n+1) → ℤ)))
    (S : Set ((EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) ×
      (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))))) (hS : MeasurableSet S)
    {C : ℝ} (hC : 0≤C)
    (hbd : ∀ p∈P, ∀ᵐ x ∂gridPairMeasureND ρ a p, ∀ w, ‖w‖=1 → ‖b x w‖≤C)
    (hcd : ∀ q∈Q, ∀ᵐ x ∂gridPairMeasureND κ a q, ∀ w, ‖w‖=1 → ‖c x w‖≤C) :
    (∫ x in (⋃ pq∈P.product Q, gridPairSetND a pq.1 ×ˢ gridPairSetND a pq.2),
      euclideanFarKernelND Ψ v b c x ∂((ρ.prod ρ).prod (κ.prod κ)).restrict S) =
      ∑ pq∈P.product Q, ∫ x, euclideanFarKernelND Ψ v b c x
        ∂((gridPairMeasureND ρ a pq.1).prod (gridPairMeasureND κ a pq.2)).restrict S := by
  have hd : ((P.product Q) : Set (((Fin (n+1) → ℤ) × (Fin (n+1) → ℤ)) ×
      ((Fin (n+1) → ℤ) × (Fin (n+1) → ℤ)))).PairwiseDisjoint
      (fun pq => gridPairSetND a pq.1 ×ˢ gridPairSetND a pq.2) := by
    intro p _ q _ hpq
    apply Set.disjoint_left.mpr
    intro z hp hq
    apply hpq
    apply Prod.ext
    · by_contra hn
      exact Set.disjoint_left.mp (gridPairSetND_disjoint hn) hp.1 hq.1
    · by_contra hn
      exact Set.disjoint_left.mp (gridPairSetND_disjoint hn) hp.2 hq.2
  have hi : ∀ pq∈P.product Q, IntegrableOn (euclideanFarKernelND Ψ v b c)
      (gridPairSetND a pq.1 ×ˢ gridPairSetND a pq.2) (((ρ.prod ρ).prod (κ.prod κ)).restrict S) := by
    intro pq hpq
    rw [IntegrableOn,← Measure.restrict_comm hS,← Measure.prod_restrict]
    change Integrable _ (((gridPairMeasureND ρ a pq.1).prod (gridPairMeasureND κ a pq.2)).restrict S)
    apply Integrable.restrict
    apply euclideanFarKernelND_integrable hΨ hs v b c hb hc _ hC
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (hbd _ (Finset.mem_product.mp hpq).1),
      Measure.quasiMeasurePreserving_snd.ae (hcd _ (Finset.mem_product.mp hpq).2)] with x hx hy
    exact ⟨hx,hy⟩
  rw [integral_biUnion_finset _ (fun pq _ => (gridPairSetND_measurable a pq.1).prod
    (gridPairSetND_measurable a pq.2)) hd hi]
  apply Finset.sum_congr rfl
  intro pq _
  rw [← Measure.restrict_comm hS,← Measure.prod_restrict]
  rfl

end Attempt4FullFar
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Set MeasureTheory Filter Real Attempt4FarGrid
open scoped ContDiff ComplexConjugate Topology ENNReal
attribute [local instance] Classical.propDecidable

theorem euclidean_far_normalized_restricted_regionND {n : ℕ} {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : ∀ t, Ψ t≠0 → t∈Ioo (1/4:ℝ) 4) (C : ℝ) (hC : 0≤C)
    {θ : ℝ} (hθ : 0<θ) (err T K : ℝ) (hK : 32*(n+2:ℝ)≤K) :
    ∃ J : ℕ, ∃ H : ℝ, 0≤H ∧ ∀ᶠ R : ℝ in atTop,
      ∀ (N : ℕ), 0<N → R=(2:ℝ)^N →
      ∀ (ρ κ : Measure (EuclideanSpace ℝ (Fin (n+1)))), ∀ [IsFiniteMeasure ρ] [IsFiniteMeasure κ],
      ∀ (a : ℝ) (k : ℕ) (P Q : Finset ((Fin (n+1) → ℤ) × (Fin (n+1) → ℤ)))
        (L₁ L₂ : Finset (Fin (n+1) → ℤ)) (X Y : Set (EuclideanSpace ℝ (Fin (n+1))))
        (v ma mb A : ℝ) (b c : (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) → EuclideanSpace ℝ (Fin (n+1)) → ℂ)
        (U W : (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) → Set (EuclideanSpace ℝ (Fin (n+1)))),
      ∀ S : Set ((EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) ×
        (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1)))),
      MeasurableSet S → v-a≤N → 1≤A → A≤R^2 →
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
          euclideanFarKernelND Ψ v b c x ∂((ρ.prod ρ).prod (κ.prod κ)).restrict S‖ ≤
        H*R^(-2*((mb-(n+1:ℝ)*k/(2*N))-(ma-(n+1:ℝ)*a/(2*N)))+4*err)*
          (farChildMaximumND ρ κ k P Q v (R^(-mb)) U W).toReal+R^(-T) := by
  have hK0 : 0≤K := by have hn : (0:ℝ)≤n := Nat.cast_nonneg n; linarith
  obtain ⟨J,H,hH,hh⟩ := euclidean_far_normalized_restricted_sumND (n := n) hΨ hs C hC hθ err T K hK0
  refine ⟨J,H,hH,hh.mono ?_⟩
  intro R hh N hN hRN ρ κ _ _ a k P Q L₁ L₂ X Y v ma mb A b c U W S hS hav hA hAup hPx hQy
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
  rw [euclideanFarKernelND_restricted_partition hΨ.continuous hs v b c hmb hmc ρ κ k P Q S hS hC hbd hcd]
  exact hh N hN hRN ρ κ a k P Q L₁ L₂ X Y v ma mb A b c U W S hS hav hA hAup hPx hQy
    hL₁ hL₂ hP hQ hs₁ hs₂ hl₁ hl₂ hu₁ hu₂ hU hW hbl hcl

end Attempt4FullFar
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Set MeasureTheory Filter Real Attempt4FarGrid
open scoped ContDiff ComplexConjugate Topology ENNReal
attribute [local instance] Classical.propDecidable

theorem euclidean_source_far_restricted_regionND {n : ℕ} {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : ∀ t, Ψ t≠0 → t∈Ioo (1/4:ℝ) 4) (C : ℝ) (hC : 0≤C)
    {σ : ℝ} (hσ : 0<σ) (hσ₁ : σ≤1) (err T K D : ℝ) (hK : 32*(n+2:ℝ)≤K) :
    ∃ J : ℕ, ∃ H : ℝ, 0≤H ∧ ∀ᶠ R : ℝ in atTop,
      ∀ (N : ℕ), 0<N → R=(2:ℝ)^N →
      ∀ (ρ κ : Measure (EuclideanSpace ℝ (Fin (n+1)))), ∀ [IsFiniteMeasure ρ] [IsFiniteMeasure κ],
      ∀ (a : ℝ) (L k : ℕ) (P Q : Finset ((Fin (n+1) → ℤ) × (Fin (n+1) → ℤ)))
        (L₁ L₂ : Finset (Fin (n+1) → ℤ)) (X Y : Set (EuclideanSpace ℝ (Fin (n+1))))
        (v ma mb : ℝ) (b c : (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) → EuclideanSpace ℝ (Fin (n+1)) → ℂ)
        (U W : (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) → Set (EuclideanSpace ℝ (Fin (n+1)))),
      ∀ S : Set ((EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) ×
        (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1)))),
      MeasurableSet S → v-a≤N → a≤k → (k:ℝ)≤v-2*(max L (Nat.ceil (10*σ*N)):ℕ)+D →
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
          euclideanFarKernelND Ψ v b c x ∂((ρ.prod ρ).prod (κ.prod κ)).restrict S‖ ≤
        H*R^(-2*((mb-(n+1:ℝ)*k/(2*N))-(ma-(n+1:ℝ)*a/(2*N)))+4*err)*
          (farChildMaximumND ρ κ k P Q v (R^(-mb)) U W).toReal+R^(-T) := by
  obtain ⟨J,H,hH,hh⟩ := euclidean_far_normalized_restricted_regionND (n := n) hΨ hs C hC hσ err T K hK
  refine ⟨J,H,hH,?_⟩
  filter_upwards [hh,far_source_point_regime_eventuallyND hσ hσ₁ D] with R hh hpoint
  intro N hN hRN ρ κ _ _ a L k P Q L₁ L₂ X Y v ma mb b c U W S hS hav hak hdepth hPx hQy
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
  exact hh N hN hRN ρ κ a k P Q L₁ L₂ X Y v ma mb A b c U W S hS hav hreg.1 hreg.2.1 hPx hQy
    hL₁ hL₂ hP hQ hs₁ hs₂ hl₁ hl₂ hu₁ hu₂ hmb hmc hU hW hbl hcl

end Attempt4FullFar
end GraphLiteralSupport
end
end

end OAI
