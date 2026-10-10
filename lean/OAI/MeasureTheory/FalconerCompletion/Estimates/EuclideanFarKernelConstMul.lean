import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Recursion.FarOriginalSet

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

lemma euclideanFarKernelND_const_mul {n : ℕ} (q : ℝ) (Ψ : ℝ → ℝ) (v : ℝ)
    (b c : (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) → EuclideanSpace ℝ (Fin (n+1)) → ℂ)
    (z : (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) ×
      (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1)))) :
    euclideanFarKernelND Ψ v (fun x w => (q:ℂ)*b x w) (fun x w => (q:ℂ)*c x w) z =
      (q:ℂ)^2*euclideanFarKernelND Ψ v b c z := by
  simp only [euclideanFarKernelND,sphereAxisIntegralND_const_mul,map_mul,Complex.conj_ofReal]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by ring

theorem euclidean_source_full_far_uniformND {n : ℕ} {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : ∀ t, Ψ t≠0 → t∈Ioo (1/4:ℝ) 4)
    {σ : ℝ} (hσ : 0<σ) (hσ₁ : σ≤1) (err T D : ℝ) (ell : ℕ)
    (hK : 32*(n+2:ℝ)≤(2:ℝ)^ell) :
    ∃ J : ℕ, ∀ C : ℝ, 0<C → ∃ H : ℝ, 0≤H ∧ ∀ᶠ R : ℝ in atTop,
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
  obtain ⟨J,H,hH,hh⟩ := euclidean_source_full_far_branchND hΨ hs 1 (by norm_num)
    hσ hσ₁ err (T+1) D ell hK
  refine ⟨J,?_⟩
  intro C hC
  refine ⟨C^2*H,by positivity,?_⟩
  filter_upwards [hh,eventually_ge_atTop (C^2),eventually_gt_atTop (0:ℝ)] with R hh hRC hR
  intro N hN hRN ρ κ _ _ a L h X Y v ma mb b c U W S hS hSG hah hav hdepth
    hl₁ hl₂ hu₁ hu₂ hmb hmc hU hW hb hc
  let b' := fun x w => ((C⁻¹:ℝ):ℂ)*b x w
  let c' := fun x w => ((C⁻¹:ℝ):ℂ)*c x w
  have hmb' : Measurable (Function.uncurry b') := measurable_const.mul hmb
  have hmc' : Measurable (Function.uncurry c') := measurable_const.mul hmc
  have hscale {f : EuclideanSpace ℝ (Fin (n+1)) → ℂ} (hf : ContDiff ℝ ∞ f)
      (hbd : ∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 →
        ‖iteratedFDeriv ℝ j f w‖≤C*(shellEffectiveScaleND L R σ)^j) :
      ∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 →
        ‖iteratedFDeriv ℝ j (fun w => ((C⁻¹:ℝ):ℂ)*f w) w‖≤1*(shellEffectiveScaleND L R σ)^j := by
    have hc' : ‖((C⁻¹:ℝ):ℂ)‖*C=1 := by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hC),inv_mul_cancel₀ hC.ne']
    have hbd' : ∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 →
        ‖iteratedFDeriv ℝ j f w‖≤C*(shellEffectiveScaleND L R σ)^(j+0) := by simpa using hbd
    simpa only [Nat.add_zero,hc'] using sphere_derivative_const_mul_bound
      (((C⁻¹:ℝ):ℂ)) hf hbd'
  have hb' : ∀ᵐ x ∂gridPairMeasureND ρ a (X,X),
      ContDiff ℝ ∞ (b' x) ∧ (∀ w∈U x, -w∈U x) ∧ tsupport (b' x) ⊆ U x ∧
      (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j (b' x) w‖≤1*(shellEffectiveScaleND L R σ)^j) := by
    filter_upwards [hb] with x hx
    exact ⟨contDiff_const.mul hx.1,hx.2.1,tsupport_mul_subset_right.trans hx.2.2.1,
      hscale hx.1 hx.2.2.2⟩
  have hc' : ∀ᵐ x ∂gridPairMeasureND κ a (Y,Y),
      ContDiff ℝ ∞ (c' x) ∧ (∀ w∈W x, -w∈W x) ∧ tsupport (c' x) ⊆ W x ∧
      (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j (c' x) w‖≤1*(shellEffectiveScaleND L R σ)^j) := by
    filter_upwards [hc] with x hx
    exact ⟨contDiff_const.mul hx.1,hx.2.1,tsupport_mul_subset_right.trans hx.2.2.1,
      hscale hx.1 hx.2.2.2⟩
  have hbound := hh N hN hRN ρ κ a L h X Y v ma mb b' c' U W S hS hSG hah hav hdepth
    hl₁ hl₂ hu₁ hu₂ hmb' hmc' hU hW hb' hc'
  have hbback : (fun x w => (C:ℂ)*b' x w)=b := by
    funext x w
    dsimp [b']
    rw [← mul_assoc,← Complex.ofReal_mul,mul_inv_cancel₀ hC.ne',Complex.ofReal_one,one_mul]
  have hcback : (fun x w => (C:ℂ)*c' x w)=c := by
    funext x w
    dsimp [c']
    rw [← mul_assoc,← Complex.ofReal_mul,mul_inv_cancel₀ hC.ne',Complex.ofReal_one,one_mul]
  have hker : euclideanFarKernelND Ψ v b c = fun z => (C:ℂ)^2*euclideanFarKernelND Ψ v b' c' z := by
    funext z
    rw [← euclideanFarKernelND_const_mul, hbback,hcback]
  have hnorm : ‖∫ x in S, euclideanFarKernelND Ψ v b c x ∂(ρ.prod ρ).prod (κ.prod κ)‖ =
      C^2*‖∫ x in S, euclideanFarKernelND Ψ v b' c' x ∂(ρ.prod ρ).prod (κ.prod κ)‖ := by
    rw [hker,integral_const_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hC]
  rw [hnorm]
  have herr : C^2*R^(-(T+1))≤R^(-T) := by
    calc
      _ ≤ R*R^(-(T+1)) := mul_le_mul_of_nonneg_right hRC (by positivity)
      _ = R^(1+(-(T+1))) := by rw [Real.rpow_add hR,Real.rpow_one]
      _ = _ := by congr 1; ring
  have hh' := mul_le_mul_of_nonneg_left hbound (sq_nonneg C)
  calc
    _ = C^2*(((2:ℝ)^((n+1:ℝ)*(v-a))/(R^(-ma))^4)*
      ‖∫ x in S, euclideanFarKernelND Ψ v b' c' x ∂(ρ.prod ρ).prod (κ.prod κ)‖) := by ring
    _ ≤ _ := by nlinarith only [hh',herr]

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

theorem euclidean_source_full_far_budgetsND {n : ℕ} {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : ∀ t, Ψ t≠0 → t∈Ioo (1/4:ℝ) 4)
    {σ : ℝ} (hσ : 0<σ) (hσ₁ : σ ≤ 1) (err T D : ℝ) (ell : ℕ)
    (hK : 32*(n+2:ℝ) ≤ (2:ℝ)^ell) :
    ∃ J : ℕ, ∀ B : ℕ → ℝ, ∃ H : ℝ, 0 ≤ H ∧ ∀ᶠ R : ℝ in atTop,
      ∀ (N : ℕ), 0<N → R=(2:ℝ)^N →
      ∀ (ρ κ : Measure (EuclideanSpace ℝ (Fin (n+1)))), ∀ [IsFiniteMeasure ρ] [IsFiniteMeasure κ],
      ∀ (a L h : ℕ) (X Y : Fin (n+1) → ℤ)
        (v ma : ℝ) (mb : ℕ → ℝ)
        (b c : (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) → EuclideanSpace ℝ (Fin (n+1)) → ℂ)
        (U W : (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) → Set (EuclideanSpace ℝ (Fin (n+1)))),
      ∀ S : Set ((EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) ×
        (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1)))),
      MeasurableSet S → S⊆farOriginalSetND a h X Y → a ≤ h → v-a ≤ N →
      ((h+ell+2:ℕ):ℝ) ≤ v-2*(max L (Nat.ceil (10*σ*N)):ℕ)+D →
      (∀ k∈Finset.Icc (a+1) (h+ell+2), ∀ i∈occupiedDescendantsND ρ a k X,
        R^(-mb k-err) ≤ (ρ (ambientGridCell k i)).toReal) →
      (∀ k∈Finset.Icc (a+1) (h+ell+2), ∀ j∈occupiedDescendantsND κ a k Y,
        R^(-mb k-err) ≤ (κ (ambientGridCell k j)).toReal) →
      (ρ (ambientGridCell a X)).toReal ≤ R^(-ma+err) →
      (κ (ambientGridCell a Y)).toReal ≤ R^(-ma+err) →
      Measurable (Function.uncurry b) → Measurable (Function.uncurry c) →
      MeasurableSet {x | euclideanPairDirectionND x∈U x} →
      MeasurableSet {x | euclideanPairDirectionND x∈W x} →
      (∀ᵐ x ∂gridPairMeasureND ρ a (X,X),
        ContDiff ℝ ∞ (b x) ∧ (∀ w∈U x, -w∈U x) ∧ tsupport (b x) ⊆ U x ∧
        (∀ j ≤ 2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j (b x) w‖ ≤ B j*(shellEffectiveScaleND L R σ)^j)) →
      (∀ᵐ x ∂gridPairMeasureND κ a (Y,Y),
        ContDiff ℝ ∞ (c x) ∧ (∀ w∈W x, -w∈W x) ∧ tsupport (c x) ⊆ W x ∧
        (∀ j ≤ 2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j (c x) w‖ ≤ B j*(shellEffectiveScaleND L R σ)^j)) →
      ((2:ℝ)^((n+1:ℝ)*(v-a))/(R^(-ma))^4)*
        ‖∫ x in S, euclideanFarKernelND Ψ v b c x ∂(ρ.prod ρ).prod (κ.prod κ)‖  ≤
        H*(∑ k∈Finset.Icc (a+1) (h+ell+2),
          R^(-2*((mb k-(n+1:ℝ)*k/(2*N))-(ma-(n+1:ℝ)*a/(2*N)))+4*err)*
            (farChildMaximumND ρ κ k (occupiedFarPairsND ρ a k ((2:ℝ)^ell) X)
              (occupiedFarPairsND κ a k ((2:ℝ)^ell) Y) v (R^(-mb k)) U W).toReal)+
          R^(-T) := by
  obtain ⟨J,hh⟩ := euclidean_source_full_far_uniformND hΨ hs hσ hσ₁ err T D ell hK
  refine ⟨J,?_⟩
  intro B
  let totalOrder := 2*(J+1)+n+3
  let C := 1+∑ j∈Finset.range (totalOrder+1), |B j|
  have hC : 0<C := by dsimp [C]; positivity
  have hBC (j : ℕ) (hj : j ≤ totalOrder) : B j ≤ C := by
    have hh := Finset.single_le_sum (s := Finset.range (totalOrder+1))
      (f := fun j => |B j|) (fun j _ => abs_nonneg (B j))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    have hj' := le_abs_self (B j)
    dsimp [C]
    linarith
  obtain ⟨H,hH,hHbound⟩ := hh C hC
  refine ⟨H,hH,?_⟩
  filter_upwards [hHbound] with R hHbound
  intro N hN hRN ρ κ _ _ a L h X Y v ma mb b c U W S hS hSG hah hav hdepth
    hl₁ hl₂ hu₁ hu₂ hmb hmc hU hW hb hc
  have hRpos : 0<R := by rw [hRN]; positivity
  have hscale : 0 ≤ shellEffectiveScaleND L R σ := by
    unfold shellEffectiveScaleND sourceMaskScaleND
    positivity
  apply hHbound N hN hRN ρ κ a L h X Y v ma mb b c U W S hS hSG hah hav hdepth
    hl₁ hl₂ hu₁ hu₂ hmb hmc hU hW
  · filter_upwards [hb] with x hx
    refine ⟨hx.1,hx.2.1,hx.2.2.1,?_⟩
    intro j hj w hw
    exact (hx.2.2.2 j hj w hw).trans (mul_le_mul_of_nonneg_right (hBC j hj) (pow_nonneg hscale j))
  · filter_upwards [hc] with x hx
    refine ⟨hx.1,hx.2.1,hx.2.2.1,?_⟩
    intro j hj w hw
    exact (hx.2.2.2 j hj w hw).trans (mul_le_mul_of_nonneg_right (hBC j hj) (pow_nonneg hscale j))

end Attempt4FullFar
end GraphLiteralSupport
end
end

end OAI
