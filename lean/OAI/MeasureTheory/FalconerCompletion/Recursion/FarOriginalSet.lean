import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Estimates.EuclideanSourceComparableFarRapid

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

def farOriginalSetND {d : ℕ} (a h : ℕ) (X Y : Fin d → ℤ) :
    Set ((EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) ×
      (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) :=
  ((ambientGridCell a X ×ˢ ambientGridCell a X) ×ˢ
    (ambientGridCell a Y ×ˢ ambientGridCell a Y)) ∩
    {x | 1/(4*(2:ℝ)^h)≤ max (dist x.1.1 x.1.2) (dist x.2.1 x.2.2)}

lemma gridPairMeasureND_mono_parent {d a k : ℕ}
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) {X : Fin d → ℤ}
    {p : (Fin d → ℤ) × (Fin d → ℤ)}
    (hp : ambientGridCell k p.1⊆ambientGridCell a X ∧ ambientGridCell k p.2⊆ambientGridCell a X) :
    gridPairMeasureND ρ k p≤gridPairMeasureND ρ a (X,X) :=
  Measure.restrict_mono_set _ (Set.prod_mono hp.1 hp.2)

theorem euclidean_source_full_far_branchND {n : ℕ} {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
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
      MeasurableSet S → S⊆farOriginalSetND a h X Y → a≤h → v-a≤N →
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
      (∀ᵐ x ∂gridPairMeasureND ρ a (X,X),
        ContDiff ℝ ∞ (b x) ∧ (∀ w∈U x, -w∈U x) ∧ tsupport (b x) ⊆ U x ∧
        (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j (b x) w‖≤C*(shellEffectiveScaleND L R σ)^j)) →
      (∀ᵐ x ∂gridPairMeasureND κ a (Y,Y),
        ContDiff ℝ ∞ (c x) ∧ (∀ w∈W x, -w∈W x) ∧ tsupport (c x) ⊆ W x ∧
        (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j (c x) w‖≤C*(shellEffectiveScaleND L R σ)^j)) →
      ((2:ℝ)^((n+1:ℝ)*(v-a))/(R^(-ma))^4)*
        ‖∫ x in S, euclideanFarKernelND Ψ v b c x ∂(ρ.prod ρ).prod (κ.prod κ)‖ ≤
        H*(∑ k∈Finset.Icc (a+1) (h+ell+2),
          R^(-2*((mb k-(n+1:ℝ)*k/(2*N))-(ma-(n+1:ℝ)*a/(2*N)))+4*err)*
            (farChildMaximumND ρ κ k (occupiedFarPairsND ρ a k ((2:ℝ)^ell) X)
              (occupiedFarPairsND κ a k ((2:ℝ)^ell) Y) v (R^(-mb k)) U W).toReal)+
          R^(-T) := by
  obtain ⟨Jc,H,hH,hcomp⟩ := euclidean_source_comparable_far_rapidND hΨ hs C hC hσ hσ₁ err (T+1) D ell hK
  obtain ⟨Jn,hnon⟩ := euclidean_source_noncomparable_regionND hΨ hs C hC hσ hσ₁ err (T+1) D
  refine ⟨max Jc Jn,H,hH,?_⟩
  filter_upwards [hcomp,hnon,eventually_ge_atTop (2:ℝ)] with R hcomp hnon hR
  intro N hN hRN ρ κ _ _ a L h X Y v ma mb b c U W S hS hSG hah hav hdepth
    hl₁ hl₂ hu₁ hu₂ hmb hmc hU hW hb hc
  let μ := (ρ.prod ρ).prod (κ.prod κ)
  let P := (ambientGridCell a X ×ˢ ambientGridCell a X) ×ˢ (ambientGridCell a Y ×ˢ ambientGridCell a Y)
  let Sc := S∩farComparableSetND a h X Y
  let Sn := S\farComparableSetND a h X Y
  let F := euclideanFarKernelND Ψ v b c
  let A := (2:ℝ)^((n+1:ℝ)*(v-a))/(R^(-ma))^4
  have hA : 0≤A := by dsimp [A]; positivity
  have hSP : S⊆P := fun _ hx => (hSG hx).1
  have hSn : MeasurableSet Sn := hS.diff (farComparableSetND_measurable a h X Y)
  have hSc : MeasurableSet Sc := hS.inter (farComparableSetND_measurable a h X Y)
  have hJc : 2*(Jc+1)+n+3≤2*(max Jc Jn+1)+n+3 := by have hh := le_max_left Jc Jn; omega
  have hJn : 2*(Jn+1)+n+3≤2*(max Jc Jn+1)+n+3 := by have hh := le_max_right Jc Jn; omega
  have hbs : ∀ᵐ z ∂μ.restrict S,
      ContDiff ℝ ∞ (b z.1) ∧ (∀ w∈U z.1, -w∈U z.1) ∧ tsupport (b z.1) ⊆ U z.1 ∧
      (∀ j≤2*(max Jc Jn+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j (b z.1) w‖≤C*(shellEffectiveScaleND L R σ)^j) := by
    apply ae_mono (Measure.restrict_mono_set μ hSP)
    rw [show μ.restrict P=(gridPairMeasureND ρ a (X,X)).prod (gridPairMeasureND κ a (Y,Y)) from (Measure.prod_restrict _ _).symm]
    exact Measure.quasiMeasurePreserving_fst.ae hb
  have hcs : ∀ᵐ z ∂μ.restrict S,
      ContDiff ℝ ∞ (c z.2) ∧ (∀ w∈W z.2, -w∈W z.2) ∧ tsupport (c z.2) ⊆ W z.2 ∧
      (∀ j≤2*(max Jc Jn+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j (c z.2) w‖≤C*(shellEffectiveScaleND L R σ)^j) := by
    apply ae_mono (Measure.restrict_mono_set μ hSP)
    rw [show μ.restrict P=(gridPairMeasureND ρ a (X,X)).prod (gridPairMeasureND κ a (Y,Y)) from (Measure.prod_restrict _ _).symm]
    exact Measure.quasiMeasurePreserving_snd.ae hc
  have hFi : IntegrableOn F S μ := by
    apply euclideanFarKernelND_integrable hΨ.continuous hs v b c hmb hmc _ hC
    filter_upwards [hbs,hcs] with z hz hz'
    constructor
    · intro w hw
      simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one] using hz.2.2.2 0 (by omega) w hw
    · intro w hw
      simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one] using hz'.2.2.2 0 (by omega) w hw
  have hbc (k : ℕ) (hk : k∈Finset.Icc (a+1) (h+ell+2))
      (p) (hp : p∈occupiedFarPairsND ρ a k ((2:ℝ)^ell) X) :
      ∀ᵐ x ∂gridPairMeasureND ρ k p,
        ContDiff ℝ ∞ (b x) ∧ (∀ w∈U x, -w∈U x) ∧ tsupport (b x) ⊆ U x ∧
        (∀ j≤2*(Jc+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j (b x) w‖≤C*(shellEffectiveScaleND L R σ)^j) := by
    have hak : a≤k := by have hh := (Finset.mem_Icc.mp hk).1; omega
    filter_upwards [ae_mono (gridPairMeasureND_mono_parent ρ (occupiedFarPairsND_geometry hak ρ hp).1) hb] with x hx
    exact ⟨hx.1,hx.2.1,hx.2.2.1,fun j hj => hx.2.2.2 j (hj.trans hJc)⟩
  have hcc (k : ℕ) (hk : k∈Finset.Icc (a+1) (h+ell+2))
      (q) (hq : q∈occupiedFarPairsND κ a k ((2:ℝ)^ell) Y) :
      ∀ᵐ x ∂gridPairMeasureND κ k q,
        ContDiff ℝ ∞ (c x) ∧ (∀ w∈W x, -w∈W x) ∧ tsupport (c x) ⊆ W x ∧
        (∀ j≤2*(Jc+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j (c x) w‖≤C*(shellEffectiveScaleND L R σ)^j) := by
    have hak : a≤k := by have hh := (Finset.mem_Icc.mp hk).1; omega
    filter_upwards [ae_mono (gridPairMeasureND_mono_parent κ (occupiedFarPairsND_geometry hak κ hq).1) hc] with x hx
    exact ⟨hx.1,hx.2.1,hx.2.2.1,fun j hj => hx.2.2.2 j (hj.trans hJc)⟩
  have hcb := hcomp N hN hRN ρ κ a L h X Y v ma mb b c U W Sc hSc Set.inter_subset_right
    hav hdepth hl₁ hl₂ hu₁ hu₂ hmb hmc hU hW hbc hcc
  have hNP : P∩Sn=Sn := inter_eq_right.mpr (Set.sdiff_subset.trans hSP)
  have hND : ∀ᵐ z ∂μ.restrict Sn,
      (2:ℝ)^(-(h:ℝ))/4≤ max (dist z.1.1 z.1.2) (dist z.2.1 z.2.2) ∧
      2*min (dist z.1.1 z.1.2) (dist z.2.1 z.2.2)≤ max (dist z.1.1 z.1.2) (dist z.2.1 z.2.2) ∧
      ContDiff ℝ ∞ (b z.1) ∧ ContDiff ℝ ∞ (c z.2) ∧
      (∀ j≤2*(Jn+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j (b z.1) w‖≤C*(shellEffectiveScaleND L R σ)^j) ∧
      (∀ j≤2*(Jn+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j (c z.2) w‖≤C*(shellEffectiveScaleND L R σ)^j) := by
    filter_upwards [ae_restrict_mem (μ := μ) hSn,
      ae_mono (Measure.restrict_mono_set μ (show Sn⊆S from Set.sdiff_subset)) hbs,
      ae_mono (Measure.restrict_mono_set μ (show Sn⊆S from Set.sdiff_subset)) hcs] with z hz hzb hzc
    have hp := hSG hz.1
    have hne : ¬ max (dist z.1.1 z.1.2) (dist z.2.1 z.2.2)≤2*min (dist z.1.1 z.1.2) (dist z.2.1 z.2.2) :=
      fun hcomp' => hz.2 ⟨hp.1,hp.2,hcomp'⟩
    have hlo : (2:ℝ)^(-(h:ℝ))/4=1/(4*(2:ℝ)^h) := by
      rw [Real.rpow_neg (by norm_num : (0:ℝ)≤2),Real.rpow_natCast]
      ring
    exact ⟨by simpa only [hlo,Set.mem_ofPred_eq] using hp.2,(lt_of_not_ge hne).le,hzb.1,hzc.1,
      fun j hj => hzb.2.2.2 j (hj.trans hJn),fun j hj => hzc.2.2.2 j (hj.trans hJn)⟩
  have hhh : (h:ℝ)≤((h+ell+2:ℕ):ℝ) := by exact_mod_cast (by omega : h≤h+ell+2)
  have hnb := hnon N hN hRN ρ κ (ambientGridCell a X) (ambientGridCell a Y) Sn a v ma L h b c
    hav (by exact_mod_cast hah) (hhh.trans hdepth) hu₁ hu₂ hmb hmc (by
      change ∀ᵐ z ∂μ.restrict (P∩Sn), _
      rw [hNP]
      exact hND)
  change Integrable F (μ.restrict (P∩Sn)) ∧ A*‖∫ z, F z ∂μ.restrict (P∩Sn)‖≤R^(-(T+1)) at hnb
  rw [hNP] at hnb
  have heq : (∫ z in Sc, F z ∂μ)+(∫ z in Sn, F z ∂μ)=(∫ z in S, F z ∂μ) :=
    integral_inter_add_sdiff (farComparableSetND_measurable a h X Y) hFi
  have hRpos : 0<R := lt_of_lt_of_le (by norm_num : (0:ℝ)<2) hR
  have herr : 2*R^(-(T+1))≤R^(-T) := by
    calc
      _ ≤ R*R^(-(T+1)) := mul_le_mul_of_nonneg_right hR (by positivity)
      _ = R^(1+(-(T+1))) := by rw [Real.rpow_add hRpos,Real.rpow_one]
      _ = _ := by congr 1; ring
  calc
    A*‖∫ z in S, F z ∂μ‖ = A*‖(∫ z in Sc, F z ∂μ)+(∫ z in Sn, F z ∂μ)‖ := by rw [heq]
    _ ≤ A*‖∫ z in Sc, F z ∂μ‖+A*‖∫ z in Sn, F z ∂μ‖ := by
      simpa only [mul_add] using mul_le_mul_of_nonneg_left (norm_add_le _ _) hA
    _ ≤ _ := by
      have hh := add_le_add hcb hnb.2
      linarith

end Attempt4FullFar
end GraphLiteralSupport
end
end

end OAI
