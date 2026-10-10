import OAI.Analysis.LipschitzHilbert.Trees.SourceCountParameters

namespace OAI

/-! The large parent reference cone is still inside the B^4 window used
by the angular-error estimate. All constants here precede the packet family. -/
noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert.SourceParameters

theorem reference_window_budget {B C radius cone : ℝ}
    (hB : 1 ≤ B) (hC : 0 ≤ C) (hradius : 0 ≤ radius) (hcone : cone ≤ C+B^3) :
    radius+cone ≤ (C+radius+1)*B^4 := by
  have hp : B^3 ≤ B^4 := pow_le_pow_right₀ hB (by norm_num)
  have hfour : 1 ≤ B^4 := one_le_pow₀ hB
  have hc := mul_le_mul_of_nonneg_left hfour (add_nonneg hC hradius)
  nlinarith

theorem branching_eq_two_pow_product (L : ℝ) :
    branching L = (2:ℝ)^(stepExponent L*blockCount L) := by
  exact (pow_mul (2:ℝ) (stepExponent L) (blockCount L)).symm

theorem branching_ge_one (L : ℝ) : 1 ≤ branching L :=
  one_le_pow₀ (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))

theorem exists_reference_window_index (C radius : ℝ) :
    ∃ J : ℕ, C+radius+1 ≤ (2:ℝ)^J := by
  obtain ⟨J,hJ⟩ := pow_unbounded_of_one_lt (C+radius+1) (by norm_num : (1:ℝ) < 2)
  exact ⟨J,hJ.le⟩

theorem eventually_reference_mask_width (C Cb : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ w W : ℝ, 0 ≤ w → branching L^2*w ≤ W → (Cb+C)*w ≤ W := by
  filter_upwards [eventually_branching_ge (max 1 (Cb+C))] with L hL
  intro w W hw hW
  have hB : 1 ≤ branching L := (le_max_left _ _).trans hL
  have hsize : Cb+C ≤ branching L^2 :=
    ((le_max_right _ _).trans hL).trans (le_self_pow₀ hB (by norm_num))
  exact (mul_le_mul_of_nonneg_right hsize hw).trans hW

end LipschitzHilbert.SourceParameters

end

end OAI
