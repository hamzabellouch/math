import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Estimates.EuclideanFarNormalizedRestrictedSum
import OAI.MeasureTheory.FalconerCompletion.Graphs.AmbientDescendants

namespace OAI

/-! Graph energies and pair estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Set MeasureTheory

lemma firstCoverBinND_ae_cover {V : Type*} [MeasurableSpace V] (μ : Measure V)
    (S : Set V) (I : Finset ℕ) (G : ℕ → Set V)
    (hcover : ∀ᵐ x ∂μ, x∈S → x∈⋃ b∈I, G b) :
    (⋃ b∈I, firstCoverBinND S I G b)=ᵐ[μ] S := by
  classical
  filter_upwards [hcover] with x hx
  apply propext
  constructor
  · intro hx'
    obtain ⟨b,_,hb⟩ := mem_iUnion₂.mp hx'
    exact (firstCoverBinND_subset S I G b hb).1
  · intro hx'
    have he : ∃ b, b∈I ∧ x∈G b := by
      obtain ⟨b,hb,hxb⟩ := mem_iUnion₂.mp (hx hx')
      exact ⟨b,hb,hxb⟩
    let b := Nat.find he
    have hb : b∈I ∧ x∈G b := Nat.find_spec he
    refine mem_iUnion₂.mpr ⟨b,hb.1,mem_firstCoverBinND.mpr ⟨hx',hb.2,?_⟩⟩
    intro c hc hcb hxc
    have hh := Nat.find_min' he (show c∈I ∧ x∈G c from ⟨hc,hxc⟩)
    exact (not_lt_of_ge hh) hcb

theorem integral_firstCoverBinND_ae {V : Type*} [MeasurableSpace V] (μ : Measure V)
    {S : Set V} (hS : MeasurableSet S) (I : Finset ℕ) (G : ℕ → Set V)
    (hG : ∀ b∈I, MeasurableSet (G b))
    (hcover : ∀ᵐ x ∂μ, x∈S → x∈⋃ b∈I, G b)
    (F : V → ℂ) (hF : IntegrableOn F S μ) :
    (∫ x in S, F x ∂μ)=∑ b∈I, ∫ x in firstCoverBinND S I G b, F x ∂μ := by
  have hh := integral_biUnion_finset I
    (fun b hb => measurableSet_firstCoverBinND hS I G hG hb)
    (firstCoverBinND_disjoint S I G)
    (fun b _ => hF.mono_set (fun x hx => (firstCoverBinND_subset S I G b hx).1))
  rw [setIntegral_congr_set (firstCoverBinND_ae_cover μ S I G hcover)] at hh
  exact hh

theorem integral_farComparable_occupied_binsND {d a h k : ℕ}
    (hK : 16*(d+1:ℝ)≤(2:ℝ)^k)
    (ρ κ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ρ] [IsFiniteMeasure κ]
    (X Y : Fin d → ℤ)
    {S : Set ((EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
      (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)))}
    (hS : MeasurableSet S) (hSsub : S⊆farComparableSetND a h X Y)
    (F : ((EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
      (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) → ℂ)
    (hF : IntegrableOn F S ((ρ.prod ρ).prod (κ.prod κ))) :
    (∫ x in S, F x ∂(ρ.prod ρ).prod (κ.prod κ))=
      ∑ b∈Finset.Icc (a+1) (h+k+2),
        ∫ x in firstCoverBinND S (Finset.Icc (a+1) (h+k+2))
          (fun b => occupiedFarRegionND ρ κ a b ((2:ℝ)^k) X Y) b,
          F x ∂(ρ.prod ρ).prod (κ.prod κ) := by
  apply integral_firstCoverBinND_ae _ hS _ _
    (fun b _ => occupiedFarRegionND_measurable ρ κ a b _ X Y) ?_ F hF
  filter_upwards [occupiedFarRegionND_ae_cover hK ρ κ X Y] with x hx hxs
  exact hx (hSsub hxs)

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

lemma occupiedDescendantsND_subset {d a k : ℕ} (hak : a≤k)
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) {X Q : Fin d → ℤ}
    (hQ : Q∈occupiedDescendantsND ρ a k X) :
    ambientGridCell k Q⊆ambientGridCell a X := by
  classical
  exact ambientDescendantsND_subset hak (Finset.mem_filter.mp hQ).1

lemma occupiedFarPairsND_geometry {d a k : ℕ} (hak : a≤k) {K : ℝ}
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) {X : Fin d → ℤ}
    {p : (Fin d → ℤ) × (Fin d → ℤ)} (hp : p∈occupiedFarPairsND ρ a k K X) :
    (ambientGridCell k p.1⊆ambientGridCell a X ∧
      ambientGridCell k p.2⊆ambientGridCell a X) ∧ farSeparatedGridND k K p.1 p.2 := by
  classical
  have hh := mem_farParentPairsND_iff.mp (Finset.mem_filter.mp hp).1
  exact ⟨⟨ambientDescendantsND_subset hak hh.1,
    ambientDescendantsND_subset hak hh.2.1⟩,hh.2.2⟩

attribute [local instance] Classical.propDecidable

theorem euclidean_source_occupied_far_binND {n : ℕ} {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : ∀ t, Ψ t≠0 → t∈Ioo (1/4:ℝ) 4) (C : ℝ) (hC : 0≤C)
    {σ : ℝ} (hσ : 0<σ) (hσ₁ : σ≤1) (err T K D : ℝ) (hK : 32*(n+2:ℝ)≤K) :
    ∃ J : ℕ, ∃ H : ℝ, 0≤H ∧ ∀ᶠ R : ℝ in atTop,
      ∀ (N : ℕ), 0<N → R=(2:ℝ)^N →
      ∀ (ρ κ : Measure (EuclideanSpace ℝ (Fin (n+1)))), ∀ [IsFiniteMeasure ρ] [IsFiniteMeasure κ],
      ∀ (a L k : ℕ) (X Y : Fin (n+1) → ℤ)
        (v ma mb : ℝ) (b c : (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) → EuclideanSpace ℝ (Fin (n+1)) → ℂ)
        (U W : (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) → Set (EuclideanSpace ℝ (Fin (n+1)))),
      ∀ S : Set ((EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) ×
        (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1)))),
      MeasurableSet S → S⊆occupiedFarRegionND ρ κ a k K X Y →
      v-a≤N → a≤k → (k:ℝ)≤v-2*(max L (Nat.ceil (10*σ*N)):ℕ)+D →
      (∀ i∈occupiedDescendantsND ρ a k X, R^(-mb-err)≤(ρ (ambientGridCell k i)).toReal) →
      (∀ j∈occupiedDescendantsND κ a k Y, R^(-mb-err)≤(κ (ambientGridCell k j)).toReal) →
      (ρ (ambientGridCell a X)).toReal≤R^(-ma+err) →
      (κ (ambientGridCell a Y)).toReal≤R^(-ma+err) →
      Measurable (Function.uncurry b) → Measurable (Function.uncurry c) →
      MeasurableSet {x | euclideanPairDirectionND x∈U x} →
      MeasurableSet {x | euclideanPairDirectionND x∈W x} →
      (∀ p∈occupiedFarPairsND ρ a k K X, ∀ᵐ x ∂gridPairMeasureND ρ k p,
        ContDiff ℝ ∞ (b x) ∧
        (∀ w∈U x, -w∈U x) ∧ tsupport (b x) ⊆ U x ∧
        (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j (b x) w‖≤C*(shellEffectiveScaleND L R σ)^j)) →
      (∀ q∈occupiedFarPairsND κ a k K Y, ∀ᵐ x ∂gridPairMeasureND κ k q,
        ContDiff ℝ ∞ (c x) ∧
        (∀ w∈W x, -w∈W x) ∧ tsupport (c x) ⊆ W x ∧
        (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j (c x) w‖≤C*(shellEffectiveScaleND L R σ)^j)) →
      ((2:ℝ)^((n+1:ℝ)*(v-a))/(R^(-ma))^4)*
        ‖∫ x in S, euclideanFarKernelND Ψ v b c x ∂(ρ.prod ρ).prod (κ.prod κ)‖ ≤
        H*R^(-2*((mb-(n+1:ℝ)*k/(2*N))-(ma-(n+1:ℝ)*a/(2*N)))+4*err)*
          (farChildMaximumND ρ κ k (occupiedFarPairsND ρ a k K X)
            (occupiedFarPairsND κ a k K Y) v (R^(-mb)) U W).toReal+R^(-T) := by
  obtain ⟨J,H,hH,hh⟩ := euclidean_source_far_restricted_regionND hΨ hs C hC hσ hσ₁ err T K D hK
  refine ⟨J,H,hH,?_⟩
  filter_upwards [hh] with R hh
  intro N hN hRN ρ κ _ _ a L k X Y v ma mb b c U W S hS hSG hav hak hdepth
    hl₁ hl₂ hu₁ hu₂ hmb hmc hU hW hb hc
  have hbound := hh N hN hRN ρ κ a L k
    (occupiedFarPairsND ρ a k K X) (occupiedFarPairsND κ a k K Y)
    (occupiedDescendantsND ρ a k X) (occupiedDescendantsND κ a k Y)
    (ambientGridCell a X) (ambientGridCell a Y) v ma mb b c U W S hS hav (by exact_mod_cast hak) hdepth
    (fun p hp => (occupiedFarPairsND_geometry hak ρ hp).1)
    (fun q hq => (occupiedFarPairsND_geometry hak κ hq).1)
    (fun _ hp => occupiedFarPairsND_first ρ hp) (fun _ hq => occupiedFarPairsND_first κ hq)
    (fun _ hp => (occupiedFarPairsND_geometry hak ρ hp).2)
    (fun _ hq => (occupiedFarPairsND_geometry hak κ hq).2)
    (fun _ hi => occupiedDescendantsND_subset hak ρ hi)
    (fun _ hj => occupiedDescendantsND_subset hak κ hj)
    hl₁ hl₂ hu₁ hu₂ hmb hmc hU hW hb hc
  change ((2:ℝ)^((n+1:ℝ)*(v-a))/(R^(-ma))^4)*
    ‖∫ x in occupiedFarRegionND ρ κ a k K X Y,
      euclideanFarKernelND Ψ v b c x ∂((ρ.prod ρ).prod (κ.prod κ)).restrict S‖ ≤ _ at hbound
  rw [Measure.restrict_restrict (occupiedFarRegionND_measurable ρ κ a k K X Y),
    inter_eq_right.mpr hSG] at hbound
  exact hbound

end Attempt4FullFar
end GraphLiteralSupport
end
end

end OAI
