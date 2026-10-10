import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.BoundedBoxConvergence
import OAI.Analysis.RieszRectifiability.Kernel.ClosedTailBounds

namespace OAI

namespace RieszRectifiability

noncomputable section

open BoxIntegral MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

def planeBoxInnerRadius (Q : ℝ≥0) (H : ℕ) : ℝ := ((H : ℝ) + 1) / ((Q : ℝ) + 1)

theorem planeBoxInnerRadius_pos (Q : ℝ≥0) (H : ℕ) : 0 < planeBoxInnerRadius Q H := by
  unfold planeBoxInnerRadius
  positivity

theorem ball_subset_boundedProjectionRegion {ι : Type*} [Fintype ι] {d : ℕ}
    (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (K Q : ℝ≥0) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e) (H : ℕ) :
    ball (e 0) (planeBoxInnerRadius Q H) ⊆ boundedProjectionRegion π (e 0) K H := by
  intro x hx
  have hH : 0 < (H : ℝ) + 1 := by positivity
  have hden : 0 < (Q : ℝ) + 1 := by positivity
  have hinner : planeBoxInnerRadius Q H ≤ (H : ℝ) + 1 := by
    unfold planeBoxInnerRadius
    apply (div_le_iff₀ hden).mpr
    nlinarith [Q.coe_nonneg]
  have hQinner : (Q : ℝ) * planeBoxInnerRadius Q H < (H : ℝ) + 1 := by
    unfold planeBoxInnerRadius
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hden).mpr
    nlinarith
  have hπdist := hπ.dist_le_mul x (e 0)
  rw [hleft 0, dist_zero_right] at hπdist
  have hnorm : ‖π x‖ < (H : ℝ) + 1 :=
    (hπdist.trans (mul_le_mul_of_nonneg_left hx.le Q.coe_nonneg)).trans_lt hQinner
  refine ⟨mem_exhaustionBox_Ioo_of_norm_lt H (π x) hnorm, ?_⟩
  apply mem_ball.mpr
  have hout : (H : ℝ) + 1 ≤ planeBoxOuterRadius K H := by
    unfold planeBoxOuterRadius
    nlinarith [K.coe_nonneg]
  exact hx.trans_le (hinner.trans hout)

theorem exists_boundedProjectionRegion_containing_ball {ι : Type*} [Fintype ι] {d : ℕ}
    (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (K Q : ℝ≥0) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e) (R : ℝ) :
    ∃ H : ℕ, ball (e 0) R ⊆ boundedProjectionRegion π (e 0) K H := by
  obtain ⟨H, hH⟩ := exists_nat_gt (((Q : ℝ) + 1) * R)
  have hden : 0 < (Q : ℝ) + 1 := by positivity
  have hR : R ≤ planeBoxInnerRadius Q H := by
    unfold planeBoxInnerRadius
    apply (le_div_iff₀ hden).mpr
    nlinarith
  exact ⟨H, (ball_subset_ball hR).trans (ball_subset_boundedProjectionRegion e π K Q hπ hleft H)⟩

theorem boundedProjectionRegion_compl_subset_exterior {ι : Type*} [Fintype ι] {d : ℕ}
    (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (K Q : ℝ≥0) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e) (H : ℕ) :
    (boundedProjectionRegion π (e 0) K H)ᶜ ⊆ closedExterior (e 0) (planeBoxInnerRadius Q H) := by
  intro x hx
  change planeBoxInnerRadius Q H ≤ dist (e 0) x
  by_contra h
  exact hx (ball_subset_boundedProjectionRegion e π K Q hπ hleft H
    (by simpa only [mem_ball, dist_comm] using! lt_of_not_ge h))

theorem eventually_ball_subset_boundedProjectionRegion {ι : Type*} [Fintype ι] {d : ℕ}
    (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (K Q : ℝ≥0) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e) (R : ℝ) :
    ∀ᶠ H : ℕ in atTop, ball (e 0) R ⊆ boundedProjectionRegion π (e 0) K H := by
  obtain ⟨H₀, hH₀⟩ := exists_nat_gt (((Q : ℝ) + 1) * R)
  filter_upwards [eventually_ge_atTop H₀] with H hH
  have hH' : (H₀ : ℝ) ≤ H := by exact_mod_cast hH
  have hR : R ≤ planeBoxInnerRadius Q H := by
    unfold planeBoxInnerRadius
    apply (le_div_iff₀ (by positivity : 0 < (Q : ℝ) + 1)).mpr
    nlinarith
  exact (ball_subset_ball hR).trans (ball_subset_boundedProjectionRegion e π K Q hπ hleft H)

end

end RieszRectifiability

end OAI
