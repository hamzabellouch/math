import OAI.Geometry.Kahler.BaseDensityPatchEstimates

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma patch_unique {P : Finset Sphere} {k : ℕ} {R : ℝ}
    (hd : (P:Set Sphere).PairwiseDisjoint (peakPatch k R)) (ξ : Sphere)
    (p : Sphere) (hp : p ∈ P) (q : Sphere) (hq : q ∈ P)
    (hξp : ξ ∈ peakPatch k R p) (hξq : ξ ∈ peakPatch k R q) : p=q := by
  by_contra hpq
  exact Set.disjoint_left.mp (hd hp hq hpq) hξp hξq

lemma density_update_value {k : ℕ} (hk : 0 < k)
    (f b : ℝ → ℝ) (W : Base → ℝ) {R F B r H c : ℝ}
    (hF : 0 ≤ F) (hB : 0 ≤ B) (hr : 0 ≤ r) (hc : 0 < c) (hc1 : 2*c ≤ 1)
    (hpos : ∀ ξ : Sphere, 0 < W ξ)
    (hT : ∀ ξ : Sphere, |phaseDerivative W ξ| ≤ (k:ℝ)*r*W ξ)
    (hf : ∀ y, 0 ≤ y → |f y| ≤ F) (hb : ∀ y, 0 ≤ y → |b y| ≤ B)
    (P : Finset Sphere) (hd : (P:Set Sphere).PairwiseDisjoint (peakPatch k R))
    (henv : ∀ p ∈ P, ∀ ξ ∈ peakPatch k R p,
      Real.exp (2*densityHeight k p ξ/k)*W (centralPoint p ξ) ≤ H*W ξ)
    (hsmall : H*(F+B*r) ≤ 1-2*c) (ξ : Sphere) :
    let V := W ξ+∑ p ∈ P, densityCorrection k R f b W p ξ
    0 < V ∧ c*W ξ ≤ V ∧ V ≤ 2*W ξ := by
  have ha : |∑ p ∈ P, densityCorrection k R f b W p ξ| ≤ (1-2*c)*W ξ := by
    apply disjoint_sum_abs_bound P (fun p => ξ ∈ peakPatch k R p) (patch_unique hd ξ) _ (by nlinarith [hpos ξ])
    · intro p hp hn
      exact ite_eq_right hn
    · intro p hp ht
      exact (densityCorrection_patch_value hk f b W hF hB hr hpos hT hf hb p ξ ht (henv p hp ξ ht)).trans
        (mul_le_mul_of_nonneg_right hsmall (hpos ξ).le)
  obtain ⟨hlo,hhi⟩ := abs_le.mp ha
  dsimp only
  have hp := hpos ξ
  have hcp : 0 < c*W ξ := mul_pos hc hp
  constructor
  · nlinarith
  constructor <;> nlinarith

lemma density_update_direction {k : ℕ} (hk : 0 < k) {R E : ℝ} (hER : E < R)
    {f b : ℝ → ℝ} {W : Base → ℝ} (hf : ContDiff ℝ ∞ f) (hb : ContDiff ℝ ∞ b) (hW : ContDiff ℝ ∞ W)
    (htail : ∀ y, E ≤ y → f y=0 ∧ b y=0)
    {F B F₁ B₁ H D : ℝ} (hF : 0 ≤ F) (hB : 0 ≤ B) (hF₁ : 0 ≤ F₁) (hB₁ : 0 ≤ B₁) (hD : 0 ≤ D) (hH : 0 ≤ H)
    (hpos : ∀ ξ : Sphere, 0 < W ξ)
    (hT : ∀ ξ : Sphere, |phaseDerivative W ξ| ≤ (k:ℝ)*W ξ)
    (hTT : ∀ ξ : Sphere, |phaseDerivative (phaseDerivative W) ξ| ≤ (k:ℝ)^2*W ξ)
    (hfv : ∀ y, 0 ≤ y → |f y| ≤ F) (hbv : ∀ y, 0 ≤ y → |b y| ≤ B)
    (hfd : ∀ y, 0 ≤ y → |deriv f y| ≤ F₁) (hbd : ∀ y, 0 ≤ y → |deriv b y| ≤ B₁)
    (P : Finset Sphere) (hd : (P:Set Sphere).PairwiseDisjoint (peakPatch k R))
    (ξ : Sphere) (v : Base)
    (hdir : ∀ p ∈ P, ξ ∈ peakPatch k R p → ‖bracket v (p:Base)/bracket (ξ:Base) (p:Base)‖ ≤ D/k)
    (henv : ∀ p ∈ P, ξ ∈ peakPatch k R p →
      Real.exp (2*densityHeight k p ξ/k)*W (centralPoint p ξ) ≤ H*W ξ) :
    |fderiv ℝ (fun z => W z+∑ p ∈ P, densityCorrection k R f b W p z) ξ v| ≤
      |fderiv ℝ W ξ v|+D*H*(4*(F+B)+F₁+B₁)*W ξ := by
  rw [fderiv_density_update hk hER hf hb hW htail]
  apply (abs_add_le _ _).trans
  apply add_le_add le_rfl
  have hw0 := (hpos ξ).le
  apply disjoint_sum_abs_bound P (fun p => ξ ∈ peakPatch k R p) (patch_unique hd ξ) _ (by positivity)
  · intro p hp hn
    rw [densityCorrection_fderiv_zero hk hER htail W p ξ hn]
    rfl
  · intro p hp ht
    exact densityCorrection_patch_direction hk hf hb hW hF hB hF₁ hB₁ hD hpos hT hTT hfv hbv hfd hbd p ξ ht v (hdir p hp ht) (henv p hp ht)

end PinchedHartogs.BaseConstruction

end

end OAI
