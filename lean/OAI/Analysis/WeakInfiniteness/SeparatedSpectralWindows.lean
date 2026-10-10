import Mathlib
import OAI.Analysis.WeakInfiniteness.SpectralWindows

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra Topology

lemma tent_support_subset (t r : ℝ) (hr : 0 < r) :
    ∀ x,spectralTent t r x ≠ 0 → x ∈ Metric.closedBall t r := by
  intro x hx
  have he : |x-t| < r := lt_of_not_ge (fun h => hx (spectralTent_zero hr h))
  simpa only [Metric.mem_closedBall,Real.dist_eq] using he.le

lemma separated_closedBalls (s t r : ℝ) :
    ∀ x ∈ Metric.closedBall s r,∀ y ∈ Metric.closedBall t r,
      dist s t-2*r ≤ dist x y := by
  intro x hx y hy
  have hx' : dist x s ≤ r := hx
  have hy' : dist y t ≤ r := hy
  have ht1 := dist_triangle s x t
  have ht2 := dist_triangle x y t
  rw [dist_comm s x] at ht1
  linarith

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A]

lemma exists_windows_of_two_nonzero_spectral_values
    (D : NonUnitalStarSubalgebra ℂ A) [IsClosed (D : Set A)]
    (π : A →⋆ₐ[ℂ] B) {U : A} (hU : IsSelfAdjoint U) (hUD : U ∈ D)
    {s t : ℝ} (hs : s ∈ spectrum ℝ (π U)) (ht : t ∈ spectrum ℝ (π U))
    (hs0 : s ≠ 0) (ht0 : t ≠ 0) (hst : s ≠ t) :
    ∃ u ∈ D,∃ v ∈ D,0 ≤ u ∧ 0 ≤ v ∧ u*v=0 ∧ π u ≠ 0 ∧ π v ≠ 0 ∧
      ∃ S T : Set ℝ,∃ ρ : ℝ,0 < ρ ∧ ContinuouslySupported U u S ∧
        ContinuouslySupported U v T ∧ (∀ x ∈ S,∀ y ∈ T,ρ ≤ dist x y) := by
  let r := min (min |s| |t|) (dist s t)/4
  have hr : 0 < r := by
    dsimp [r]
    exact div_pos (lt_min (lt_min (abs_pos.mpr hs0) (abs_pos.mpr ht0)) (dist_pos.mpr hst)) (by norm_num)
  have hrs : r ≤ |s| := by
    have := (min_le_left (min |s| |t|) (dist s t)).trans (min_le_left |s| |t|)
    dsimp [r]; linarith [abs_nonneg s]
  have hrt : r ≤ |t| := by
    have := (min_le_left (min |s| |t|) (dist s t)).trans (min_le_right |s| |t|)
    dsimp [r]; linarith [abs_nonneg t]
  have hrst : 2*r < dist s t := by
    have := min_le_right (min |s| |t|) (dist s t)
    dsimp [r] at hr ⊢; linarith
  let f : C(ℝ,ℝ) := ⟨spectralTent s r,spectralTent_continuous s r⟩
  let g : C(ℝ,ℝ) := ⟨spectralTent t r,spectralTent_continuous t r⟩
  have hf0 : f 0=0 := spectralTent_zero hr (by simpa using hrs)
  have hg0 : g 0=0 := spectralTent_zero hr (by simpa using hrt)
  have hfg : cfc f U*cfc g U=0 := by
    rw [← cfc_mul f g U f.continuous.continuousOn g.continuous.continuousOn]
    calc
      cfc (fun x => f x*g x) U=cfc (0 : ℝ → ℝ) U := by
        apply cfc_congr
        intro x _
        change f x*g x=0
        by_cases hfx : f x=0
        · rw [hfx,zero_mul]
        by_cases hgx : g x=0
        · rw [hgx,mul_zero]
        have hx := separated_closedBalls s t r x (tent_support_subset s r hr x hfx)
          x (tent_support_subset t r hr x hgx)
        rw [dist_self] at hx
        exfalso; linarith
      _ = 0 := cfc_zero ℝ U
  refine ⟨cfc f U,cfc_mem_of_zero D hUD f hf0,cfc g U,cfc_mem_of_zero D hUD g hg0,
    cfc_nonneg (fun x _ => spectralTent_nonneg s r x),
    cfc_nonneg (fun x _ => spectralTent_nonneg t r x),hfg,
    cfc_nonzero_of_spectral_value π hU f hs ?_,
    cfc_nonzero_of_spectral_value π hU g ht ?_,Metric.closedBall s r,Metric.closedBall t r,
    dist s t-2*r,sub_pos.mpr hrst,continuouslySupported_cfc U f _ (tent_support_subset s r hr),
    continuouslySupported_cfc U g _ (tent_support_subset t r hr),separated_closedBalls s t r⟩
  · change spectralTent s r s ≠ 0
    rw [spectralTent_center]; exact one_ne_zero
  · change spectralTent t r t ≠ 0
    rw [spectralTent_center]; exact one_ne_zero

end

end WeakPureInfiniteness
end

end OAI
