import Mathlib
import OAI.Analysis.Conductivity.Sobolev.CompactLipschitzH1
import OAI.Analysis.Conductivity.Geometry.CollarLip
import OAI.Analysis.Conductivity.Geometry.CollarInteriorFacts

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped NNReal

lemma lipschitz_mul_real_bounded {X : Type*} [PseudoMetricSpace X]
    {f g : X → ℝ} {K L A B : ℝ≥0} (hf : LipschitzWith K f) (hg : LipschitzWith L g)
    (hA : ∀ x,|f x|≤A) (hB : ∀ x,|g x|≤B) :
    LipschitzWith (K*B+A*L) (fun x => f x*g x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  have he : f x*g x-f y*g y=(f x-f y)*g x+f y*(g x-g y) := by ring
  rw [he]
  calc
    _ ≤ |(f x-f y)*g x|+|f y*(g x-g y)| := abs_add_le _ _
    _ = |f x-f y| *|g x|+|f y| *|g x-g y| := by rw [abs_mul,abs_mul]
    _ ≤ (K*dist x y)*B+A*(L*dist x y) := add_le_add
      (mul_le_mul (by simpa only [Real.dist_eq] using hf.dist_le_mul x y) (hB x) (abs_nonneg _) (by positivity))
      (mul_le_mul (hA y) (by simpa only [Real.dist_eq] using hg.dist_le_mul x y) (abs_nonneg _) (by positivity))
    _ = _ := by push_cast; ring

lemma compact_cut_positive_lipschitz {τ χ : (Fin 3 → ℝ) → ℝ} {K : ℝ≥0}
    (hτ : LipschitzWith K τ) (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ)
    (hc : HasCompactSupport χ) (hχb : ∀ x,|χ x|≤1)
    {M : ℝ} (hM : 0≤M) (hb : ∀ x∈tsupport χ,τ x≤M) :
    ∃ C,LipschitzWith C (fun x => χ x*max 0 (τ x)) := by
  obtain ⟨C,hC⟩ := hχ.lipschitzWith_of_hasCompactSupport hc (by simp)
  have hr := (LipschitzWith.const (0:ℝ)).max (hτ.min (LipschitzWith.const M))
  have hbound (x : Fin 3 → ℝ) : |max 0 (min (τ x) M)|≤(⟨M,hM⟩:ℝ≥0) := by
    rw [abs_of_nonneg (le_max_left _ _)]
    exact max_le hM (min_le_right _ _)
  have H := lipschitz_mul_real_bounded hC hr (A:=1) (B:=(⟨M,hM⟩ : ℝ≥0)) (by simpa using hχb) hbound
  have he : (fun x => χ x*max 0 (τ x))=(fun x => χ x*max 0 (min (τ x) M)) := by
    funext x
    by_cases hx : x∈tsupport χ
    · rw [min_eq_left (hb x hx)]
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
  have H' : ∃ D,LipschitzWith D (fun x => χ x*max 0 (min (τ x) M)) := ⟨_,H⟩
  rwa [←he] at H'

theorem compact_collar_slope_H1 {χ : (Fin 3 → ℝ) → ℝ}
    (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hc : HasCompactSupport χ) (hχb : ∀ x,|χ x|≤1)
    (a b κ l r : ℝ) (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (hχs : tsupport χ⊆sourceClosedCollarBand l r) :
    let f := fun x : R3 => κ*(χ (WithLp.ofLp x)*max 0 (a*(sourceCollarTime (WithLp.ofLp x)-b)))
    ∃ w : H1,w∈H10 ∧ (∀ᵐ x∂ballMeasure,
      weakValue w x=f x ∧ ∀ i,weakGradient w x i=lineDeriv ℝ f x (EuclideanSpace.single i 1)) := by
  obtain ⟨K,hK⟩ := attachedEndTime_lipschitz a b
  have hb (x : Fin 3 → ℝ) (hx : x∈tsupport χ) :
      a*(sourceCollarTime x-b)≤|a| *(|l|+|r|+|b|) := by
    have ht := hχs hx
    have hav : |sourceCollarTime x|≤|l|+|r| := by
      apply abs_le.mpr
      constructor
      · linarith [(neg_abs_le l).trans ht.1,abs_nonneg r]
      · linarith [ht.2.trans (le_abs_self r),abs_nonneg l]
    exact (le_abs_self _).trans (by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (show |sourceCollarTime x| + |b| ≤ |l|+|r|+|b| by linarith)) (abs_nonneg _))
  obtain ⟨C,hC⟩ := compact_cut_positive_lipschitz hK hχ hc hχb (by positivity) hb
  let E : R3 ≃L[ℝ] (Fin 3 → ℝ) := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  have H := (ContinuousLinearMap.toSpanSingleton ℝ κ).lipschitzWith.comp (hC.comp E.lipschitzWith)
  have hF : LipschitzWith (‖ContinuousLinearMap.toSpanSingleton ℝ κ‖₊ * (C * ‖E.toContinuousLinearMap‖₊))
      (fun x : R3 => κ*(χ (WithLp.ofLp x)*max 0 (a*(sourceCollarTime (WithLp.ofLp x)-b)))) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Function.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,E,
      PiLp.coe_continuousLinearEquiv,smul_eq_mul,mul_comm] using H.dist_le_mul x y
  apply compact_lipschitz_H1 hF (by norm_num : (5:ℝ)/2<3)
  intro x hx
  have hn : WithLp.ofLp x∉tsupport χ := by
    intro hs
    have hh := sourceBand_euclidean_bound (show WithLp.ofLp x∈sourceClosedCollarBand (-(1:ℝ)/100) (1/100) from
      ⟨hl.trans (hχs hs).1,(hχs hs).2.trans hr⟩)
    exact not_le_of_gt hx hh
  simp [image_eq_zero_of_notMem_tsupport hn]

end ScalarConductivity

end

end OAI
