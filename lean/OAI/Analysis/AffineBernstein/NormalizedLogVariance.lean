import Mathlib
import OAI.Analysis.AffineBernstein.NormalizedFamilyDet
import OAI.Analysis.AffineBernstein.WeightedPoincare
import OAI.Analysis.AffineBernstein.LogVariance

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section NormalizedLogVariance

/-- Literal normalized solution data, produced by the actual centered section maps. -/
structure BalancedNormalized {n : ℕ} (ρ R : ℝ) (v : Space n → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ v
  posDef : ∀ x, (hessian v x).PosDef
  maximal : AffineMaximalOn univ v
  zero : v 0 = 0
  deriv_zero : fderiv ℝ v 0 = 0
  balance : SectionBalance univ v ρ
  inner : Metric.ball 0 1 ⊆ tangentSection univ v 0 1
  outer : tangentSection univ v 0 1 ⊆ Metric.ball 0 R

lemma normalized_gradient_bound {n : ℕ} {ρ R : ℝ} {v : Space n → ℝ}
    (hv : BalancedNormalized ρ R v) {x : Space n}
    (hx : x ∈ Metric.closedBall (0:Space n) (1/4:ℝ)) :
    ‖fderiv ℝ v x‖ ≤ 4 := by
  have hcv := convexOn_of_hessian_posSemidef isOpen_univ convex_univ hv.smooth.contDiffOn
    (fun y _ => (hv.posDef y).posSemidef)
  have hxn : ‖x‖ ≤ (1/4:ℝ) := by simpa only [Metric.mem_closedBall,dist_zero_right] using hx
  have hbase : x ∈ Metric.ball (0:Space n) 1 := by
    rw [Metric.mem_ball,dist_zero_right]; linarith
  have hnb : Metric.closedBall x (1/2:ℝ) ⊆ Metric.ball 0 1 := by
    intro y hy
    have hyn : ‖y-x‖ ≤ (1/2:ℝ) := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hy
    rw [Metric.mem_ball,dist_zero_right]
    have hh := norm_add_le (y-x) x
    rw [sub_add_cancel] at hh
    linarith
  have hb : ∀ y ∈ Metric.ball (0:Space n) 1, |v y| ≤ 1 := by
    intro y hy
    have h0 : 0 ≤ v y := by
      have H := tangentHeight_nonneg isOpen_univ convex_univ hv.smooth.contDiffOn
        (fun z _ => hv.posDef z) (mem_univ 0) (mem_univ y)
      simpa [tangentHeight,hv.zero,hv.deriv_zero] using H
    have h1 : v y < 1 := by
      have H := (hv.inner hy).2
      simpa [tangentHeight,hv.zero,hv.deriv_zero] using H
    rw [abs_of_nonneg h0]
    exact h1.le
  have H := norm_fderiv_le_of_convex_bounded
    (hcv.subset (subset_univ _) (convex_ball _ _)) hbase
    (hv.smooth.differentiable (by simp) x) (by norm_num : (0:ℝ)<1/2)
    (by norm_num : (0:ℝ)≤1) hnb hb
  norm_num at H ⊢
  exact H

lemma normalized_gradient_chord_bound {n : ℕ} {ρ R : ℝ} {v : Space n → ℝ}
    (hv : BalancedNormalized ρ R v) {x y : Space n}
    (hx : x ∈ Metric.closedBall (0:Space n) (1/16:ℝ))
    (hy : y ∈ Metric.closedBall (0:Space n) (1/16:ℝ)) :
    (fderiv ℝ v y-fderiv ℝ v x) (y-x) ≤ 1 := by
  have hxq := (Metric.closedBall_subset_closedBall (by norm_num : (1/16:ℝ)≤1/4)) hx
  have hyq := (Metric.closedBall_subset_closedBall (by norm_num : (1/16:ℝ)≤1/4)) hy
  have hd : ‖fderiv ℝ v y-fderiv ℝ v x‖ ≤ 8 :=
    (norm_sub_le _ _).trans (by linarith [normalized_gradient_bound hv hxq,normalized_gradient_bound hv hyq])
  have hs : ‖y-x‖ ≤ (1/8:ℝ) := by
    have hxn : ‖x‖ ≤ (1/16:ℝ) := by simpa only [Metric.mem_closedBall,dist_zero_right] using hx
    have hyn : ‖y‖ ≤ (1/16:ℝ) := by simpa only [Metric.mem_closedBall,dist_zero_right] using hy
    exact (norm_sub_le _ _).trans (by linarith)
  calc
    _ ≤ ‖(fderiv ℝ v y-fderiv ℝ v x) (y-x)‖ := le_abs_self _
    _ ≤ ‖fderiv ℝ v y-fderiv ℝ v x‖*‖y-x‖ := (fderiv ℝ v y-fderiv ℝ v x).le_opNorm _
    _ ≤ 8*(1/8:ℝ) := mul_le_mul hd hs (norm_nonneg _) (by norm_num)
    _ = 1 := by norm_num

/-- Uniform logarithmic variance for the *actual* inverse-Hessian operator.
The determinant bounds and all geometric constant dependencies are outputs. -/
theorem normalized_log_variance {n : ℕ} {ρ R : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hR : 1 ≤ R) :
    ∃ V : ℝ, 0 ≤ V ∧ ∀ v : Space n → ℝ, BalancedNormalized ρ R v →
      ∀ s : Space n → ℝ, ContDiff ℝ ∞ s → (∀ x, 0 < s x) →
      (∀ x, inverseHessianTrace v s x ≤ 0) →
      (∫ x in Metric.closedBall (0:Space n) (1/16:ℝ),
        ∫ y in Metric.closedBall (0:Space n) (1/16:ℝ),
          (Real.log (s y)-Real.log (s x))^2) ≤ V := by
  obtain ⟨c,C,hc,hC,Hdet⟩ := normalized_balanced_det_bounds hρ hρ1 hR (n := n)
  let η : ContDiffBump (0:Space n) := ⟨1/16,1/4,by norm_num,by norm_num⟩
  let K := Metric.closedBall (0:Space n) (1/16:ℝ)
  let B := Metric.closedBall (0:Space n) (1/4:ℝ)
  have hη : ContDiff ℝ ∞ (η : Space n → ℝ) := η.contDiff
  have hg : Continuous (gradientSquared (η : Space n → ℝ)) := by
    unfold gradientSquared
    exact continuous_finsetSum _ (fun _ _ => ((contDiff_dirDeriv hη _).continuous.pow 2))
  obtain ⟨M,hMb⟩ := (isCompact_closedBall (0:Space n) (1/4:ℝ)).bddAbove_image hg.continuousOn
  have hM (x : Space n) (hx : x ∈ B) : gradientSquared (η : Space n → ℝ) x ≤ M := hMb ⟨x,hx,rfl⟩
  have hMn : 0 ≤ M := (gradientSquared_nonneg (η : Space n → ℝ) 0).trans
    (hM 0 (by simp [B]))
  let J := ((n:ℝ)+1)*(volume (Metric.closedBall (0:Space n) (4+(1/4:ℝ)))).toReal
  let V := (volume K).toReal*(2:ℝ)^n*(4*M*J/c)
  have hJn : 0 ≤ J := by dsimp [J]; positivity
  refine ⟨V,by dsimp [V]; positivity,?_⟩
  intro v hv s hs hspos hLs
  have hcK : ∀ x ∈ K, c ≤ (hessian v x).det := by
    intro x hx
    have hxn : ‖x‖ ≤ (1/16:ℝ) := by simpa only [K,Metric.mem_closedBall,dist_zero_right] using hx
    exact (Hdet v hv.smooth hv.posDef hv.maximal hv.zero hv.deriv_zero hv.balance hv.inner hv.outer x
      (by rw [Metric.mem_ball,dist_zero_right]; linarith)).1
  have hcof : (∫ x in B, (hessian v x).det*(hessian v x)⁻¹.trace) ≤ J := by
    apply integral_cofactor_trace_le_ball hv.smooth hv.posDef (isCompact_closedBall _ _)
    · intro x hx
      simpa only [gradient,LinearIsometryEquiv.norm_map] using normalized_gradient_bound hv hx
    · intro x hx
      simpa only [B,Metric.mem_closedBall,dist_zero_right] using hx
  have he := log_energy_le_cutoff hv.smooth hv.posDef hs hspos hLs hη η.hasCompactSupport
    (isCompact_closedBall (0:Space n) (1/16:ℝ)) (isCompact_closedBall (0:Space n) (1/4:ℝ))
    (by rw [η.tsupport_eq]) (fun x hx => η.one_of_mem_closedBall hx)
    hc hMn hcK hM hcof
  have hw := weighted_poincare hv.smooth (hs.log (fun x => (hspos x).ne')) hv.posDef
    (isCompact_closedBall (0:Space n) (1/16:ℝ)) (convex_closedBall _ _) (by norm_num : (0:ℝ)≤1)
    (fun x hx y hy => normalized_gradient_chord_bound hv hx hy)
  simp only [one_mul] at hw
  exact hw.trans (mul_le_mul_of_nonneg_left he (by positivity))

end NormalizedLogVariance


end
end AffineBernstein
end

end OAI
