import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.FirstCoverBinAeCover

namespace OAI

/-! Recursive policies and quantitative depth estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Set MeasureTheory Filter Real Attempt4FarGrid
open scoped ContDiff ComplexConjugate Topology ENNReal
attribute [local instance] Classical.propDecidable

lemma euclideanFarKernelND_occupied_integrable {n : ℕ} {Ψ : ℝ → ℝ} (hΨ : Continuous Ψ)
    (hs : ∀ t, Ψ t≠0 → t∈Ioo (1/4:ℝ) 4) (v : ℝ)
    (b c : (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) → EuclideanSpace ℝ (Fin (n+1)) → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    (ρ κ : Measure (EuclideanSpace ℝ (Fin (n+1)))) [IsFiniteMeasure ρ] [IsFiniteMeasure κ]
    (a k : ℕ) (K : ℝ) (X Y : Fin (n+1) → ℤ) {C : ℝ} (hC : 0≤C)
    (hbd : ∀ p∈occupiedFarPairsND ρ a k K X,
      ∀ᵐ x ∂gridPairMeasureND ρ k p, ∀ w, ‖w‖=1 → ‖b x w‖≤C)
    (hcd : ∀ q∈occupiedFarPairsND κ a k K Y,
      ∀ᵐ x ∂gridPairMeasureND κ k q, ∀ w, ‖w‖=1 → ‖c x w‖≤C) :
    IntegrableOn (euclideanFarKernelND Ψ v b c) (occupiedFarRegionND ρ κ a k K X Y)
      ((ρ.prod ρ).prod (κ.prod κ)) := by
  change IntegrableOn _ (⋃ pq∈(occupiedFarPairsND ρ a k K X).product (occupiedFarPairsND κ a k K Y),
    gridPairSetND k pq.1 ×ˢ gridPairSetND k pq.2) _
  apply integrableOn_finset_iUnion.mpr
  intro pq hpq
  rw [IntegrableOn,← Measure.prod_restrict]
  change Integrable _ ((gridPairMeasureND ρ k pq.1).prod (gridPairMeasureND κ k pq.2))
  apply euclideanFarKernelND_integrable hΨ hs v b c hb hc _ hC
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (hbd _ (Finset.mem_product.mp hpq).1),
    Measure.quasiMeasurePreserving_snd.ae (hcd _ (Finset.mem_product.mp hpq).2)] with x hx hy
  exact ⟨hx,hy⟩

theorem euclidean_source_comparable_far_branchND {n : ℕ} {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
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
          ((Finset.Icc (a+1) (h+ell+2)).card:ℝ)*R^(-T) := by
  obtain ⟨J,H,hH,hh⟩ := euclidean_source_occupied_far_binND hΨ hs C hC hσ hσ₁ err T ((2:ℝ)^ell) D hK
  refine ⟨J,H,hH,?_⟩
  filter_upwards [hh] with R hh
  intro N hN hRN ρ κ _ _ a L h X Y v ma mb b c U W S hS hSG hav hdepth
    hl₁ hl₂ hu₁ hu₂ hmb hmc hU hW hb hc
  let I := Finset.Icc (a+1) (h+ell+2)
  let G := fun k => occupiedFarRegionND ρ κ a k ((2:ℝ)^ell) X Y
  let B := firstCoverBinND S I G
  let F := euclideanFarKernelND Ψ v b c
  let μ := (ρ.prod ρ).prod (κ.prod κ)
  let A := (2:ℝ)^((n+1:ℝ)*(v-a))/(R^(-ma))^4
  have hA : 0≤A := by dsimp [A]; positivity
  have hK' : 16*((n+1:ℕ)+1:ℝ)≤(2:ℝ)^ell := by push_cast; have hn : (0:ℝ)≤n := Nat.cast_nonneg n; linarith
  have hgi (k : ℕ) (hk : k∈I) : IntegrableOn F (G k) μ := by
    apply euclideanFarKernelND_occupied_integrable hΨ.continuous hs v b c hmb hmc ρ κ a k ((2:ℝ)^ell) X Y hC
    · intro p hp
      filter_upwards [hb k hk p hp] with x hx w hw
      simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one] using hx.2.2.2 0 (by omega) w hw
    · intro q hq
      filter_upwards [hc k hk q hq] with x hx w hw
      simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one] using hx.2.2.2 0 (by omega) w hw
  have hFi : IntegrableOn F S μ := by
    apply (integrableOn_finset_iUnion.mpr hgi).mono_set_ae
    filter_upwards [occupiedFarRegionND_ae_cover hK' ρ κ X Y] with x hx hxs
    exact hx (hSG hxs)
  have hsum : (∫ x in S, F x ∂μ)=∑ k∈I, ∫ x in B k, F x ∂μ :=
    integral_farComparable_occupied_binsND hK' ρ κ X Y hS hSG F hFi
  have hbi (k : ℕ) (hk : k∈I) :
      A*‖∫ x in B k, F x ∂μ‖ ≤
        H*R^(-2*((mb k-(n+1:ℝ)*k/(2*N))-(ma-(n+1:ℝ)*a/(2*N)))+4*err)*
          (farChildMaximumND ρ κ k (occupiedFarPairsND ρ a k ((2:ℝ)^ell) X)
            (occupiedFarPairsND κ a k ((2:ℝ)^ell) Y) v (R^(-mb k)) U W).toReal+R^(-T) := by
    have hak : a≤k := by have hh := (Finset.mem_Icc.mp hk).1; omega
    have hkmax : (k:ℝ)≤((h+ell+2:ℕ):ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hk).2
    exact hh N hN hRN ρ κ a L k X Y v ma (mb k) b c U W (B k)
      (measurableSet_firstCoverBinND hS I G (fun j _ => occupiedFarRegionND_measurable ρ κ a j _ X Y) hk)
      (fun x hx => (firstCoverBinND_subset S I G k hx).2)
      hav hak (hkmax.trans hdepth) (hl₁ k hk) (hl₂ k hk) hu₁ hu₂ hmb hmc hU hW (hb k hk) (hc k hk)
  calc
    A*‖∫ x in S, F x ∂μ‖ = A*‖∑ k∈I, ∫ x in B k, F x ∂μ‖ := by rw [hsum]
    _ ≤ A*(∑ k∈I, ‖∫ x in B k, F x ∂μ‖) :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) hA
    _ = ∑ k∈I, A*‖∫ x in B k, F x ∂μ‖ := Finset.mul_sum ..
    _ ≤ ∑ k∈I, (H*R^(-2*((mb k-(n+1:ℝ)*k/(2*N))-(ma-(n+1:ℝ)*a/(2*N)))+4*err)*
          (farChildMaximumND ρ κ k (occupiedFarPairsND ρ a k ((2:ℝ)^ell) X)
            (occupiedFarPairsND κ a k ((2:ℝ)^ell) Y) v (R^(-mb k)) U W).toReal+R^(-T)) :=
      Finset.sum_le_sum hbi
    _ = _ := by simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,Finset.mul_sum,mul_assoc,I]

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
open Set Filter Real
open scoped Topology

lemma far_depth_card_leND {a u N : ℕ} {v D : ℝ}
    (hu : (u:ℝ)≤v+D) (hv : v-a≤N) :
    ((Finset.Icc (a+1) u).card:ℝ)≤N+|D| := by
  have hcard : (Finset.Icc (a+1) u).card=u-a := by
    rw [Nat.card_Icc,Nat.add_sub_add_right]
  rw [hcard]
  by_cases hau : a≤u
  · rw [Nat.cast_sub hau]
    linarith [le_abs_self D]
  · rw [Nat.sub_eq_zero_of_le (by omega : u≤a),Nat.cast_zero]
    positivity

theorem far_depth_error_eventuallyND (D T : ℝ) :
    ∀ᶠ R : ℝ in atTop, ∀ (N a u : ℕ) (v : ℝ), R=(2:ℝ)^N →
      (u:ℝ)≤v+D → v-a≤N →
      ((Finset.Icc (a+1) u).card:ℝ)*R^(-(T+1))≤R^(-T) := by
  filter_upwards [eventually_ge_atTop (max 1 (2*|D|))] with R hR
  intro N a u v hRN hu hv
  have hRpos : 0<R := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) ((le_max_left _ _).trans hR)
  have hND : (N:ℝ)+|D|≤R := by
    have hn : 2*(N:ℝ)≤(2:ℝ)^N := by exact_mod_cast Nat.mul_le_pow (by decide : 2≠1) N
    rw [← hRN] at hn
    have hd := (le_max_right 1 (2*|D|)).trans hR
    linarith
  calc
    _ ≤ R*R^(-(T+1)) := mul_le_mul_of_nonneg_right ((far_depth_card_leND hu hv).trans hND) (by positivity)
    _ = R^(1+(-(T+1))) := by rw [Real.rpow_add hRpos,Real.rpow_one]
    _ = _ := by congr 1; ring

end Attempt4FullFar
end GraphLiteralSupport
end
end

end OAI
