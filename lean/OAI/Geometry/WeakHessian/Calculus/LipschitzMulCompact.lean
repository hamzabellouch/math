import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.L2SlopeGraph
import OAI.Geometry.WeakHessian.LocalBounds.SlopeApproxProduct

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set
open scoped NNReal
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open Set
open scoped NNReal ENNReal

variable {X : Type*} [MetricSpace X]

lemma lipschitz_mul_compact {φ f : X → ℝ} (hφ : GloballyLipschitz φ)
    (hf : GloballyLipschitz f) (hc : HasCompactSupport φ) :
    GloballyLipschitz (fun x => φ x*f x) := by
  obtain ⟨A,hA⟩ := hc.isCompact.image hφ.choose_spec.continuous |>.isBounded.subset_closedBall 0
  obtain ⟨B,hB⟩ := hc.isCompact.image hf.choose_spec.continuous |>.isBounded.subset_closedBall 0
  obtain ⟨n,hn⟩ := exists_nat_ge B
  let g := fun x => max (-(n:ℝ)) (min (f x) n)
  have hg : LipschitzWith hf.choose g :=
    (hf.choose_spec.min_const (n:ℝ)).const_max (-(n:ℝ))
  have hgb (x : X) : |g x| ≤ (n:ℝ) :=
    abs_le.mpr ⟨le_max_left _ _,max_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) (min_le_right _ _)⟩
  have hφb (x : X) : |φ x| ≤ |A| := by
    by_cases hx : φ x = 0
    · simp [hx]
    · have hx' := hA (mem_image_of_mem _ (subset_tsupport _ (Function.mem_support.mpr hx)))
      simp only [Metric.mem_closedBall,dist_zero_right,Real.norm_eq_abs] at hx'
      exact hx'.trans (le_abs_self A)
  have heq : (fun x => φ x*f x) = (fun x => φ x*g x) := by
    funext x
    by_cases hx : φ x = 0
    · simp [hx]
    have hb := hB (mem_image_of_mem _ (subset_tsupport _ (Function.mem_support.mpr hx)))
    simp only [Metric.mem_closedBall,dist_zero_right,Real.norm_eq_abs] at hb
    have hb' := abs_le.mp (hb.trans hn)
    simp only [g,min_eq_left hb'.2,max_eq_right hb'.1]
  rw [heq]
  exact ⟨_,lipschitz_mul_bounded hφ.choose_spec hg hφb hgb⟩

lemma localSlope_add_const (f : X → ℝ) (a : ℝ) (x : X) :
    localSlope (fun y => f y+a) x = localSlope f x := by
  unfold localSlope
  congr 1
  funext y
  congr 2
  ring_nf

lemma localSlope_mix_le {φ f g : X → ℝ}
    (hφ : GloballyLipschitz φ) (hf : GloballyLipschitz f) (hg : GloballyLipschitz g)
    (x : X) (hφ0 : 0 ≤ φ x) (hφ1 : φ x ≤ 1) :
    (localSlope (fun y => φ y*f y+(1-φ y)*g y) x).toReal ≤
      φ x*(localSlope f x).toReal+(1-φ x)*(localSlope g x).toReal+
        |f x-g x| * (localSlope φ x).toReal := by
  let u : X → ℝ := fun y => φ x*f y+(1-φ x)*g y
  let v : X → ℝ := fun y => (φ y-φ x)*(f y-g y)
  have heq : (fun y => φ y*f y+(1-φ y)*g y) = (fun y => u y+v y) := by
    funext y; dsimp only [u,v]; ring
  have hu : localSlope u x ≤ ENNReal.ofReal (φ x)*localSlope f x+
      ENNReal.ofReal (1-φ x)*localSlope g x := by
    have H := localSlope_add_le (fun y => φ x*f y) (fun y => (1-φ x)*g y) x
    simpa only [localSlope_const_mul,abs_of_nonneg hφ0,abs_of_nonneg (sub_nonneg.mpr hφ1)] using H
  have hv : localSlope v x ≤ ENNReal.ofReal |f x-g x| * localSlope φ x := by
    have H := localSlope_product_le (hφ.choose_spec.sub (LipschitzWith.const (φ x)))
      (hf.choose_spec.sub hg.choose_spec) x
    simp only [sub_self,abs_zero,ENNReal.ofReal_zero,zero_mul,zero_add] at H
    have hc : localSlope (fun y => φ y-φ x) x = localSlope φ x := by
      simpa only [sub_eq_add_neg] using localSlope_add_const φ (-φ x) x
    rwa [hc] at H
  have H := (localSlope_add_le u v x).trans (add_le_add hu hv)
  rw [← heq] at H
  have hf0 := localSlope_ne_top hf x
  have hg0 := localSlope_ne_top hg x
  have hφt := localSlope_ne_top hφ x
  have ha0 : ENNReal.ofReal (φ x)*localSlope f x ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf0
  have hb0 : ENNReal.ofReal (1-φ x)*localSlope g x ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hg0
  have hc0 : ENNReal.ofReal |f x-g x| * localSlope φ x ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hφt
  have HT := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ha0,hb0⟩,hc0⟩) H
  simpa only [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨ha0,hb0⟩) hc0,
    ENNReal.toReal_add ha0 hb0,ENNReal.toReal_mul,ENNReal.toReal_ofReal hφ0,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hφ1),ENNReal.toReal_ofReal (abs_nonneg _)] using HT
end WeakHessian

end
end InlinedFile0

end OAI
