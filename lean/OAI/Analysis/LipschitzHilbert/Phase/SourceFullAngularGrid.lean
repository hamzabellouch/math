import OAI.Analysis.LipschitzHilbert.Phase.AngularGrid
import OAI.Analysis.LipschitzHilbert.Trees.SourceParameters

namespace OAI

/-! A common source grid for every row of a finite collection. Its root
is chosen after the row precisions; no extra eligibility hypothesis is
needed in the application of the packet recovery theorem. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem exists_source_full_angular_grid {ι : Type*} [Fintype ι]
    (L : ℝ) (hL : 1 ≤ L) (precision : ι → ℝ)
    (hp : ∀ i, 0 ≤ precision i) :
    ∃ g : AngularGrid, (g.branching : ℝ) = SourceParameters.step L ∧
      2 ≤ g.rootWidth ∧
      ∀ i, g.eligible (g.rootWidth / SourceParameters.branching L ^ 2) (precision i) 0 := by
  classical
  have he : 0 < SourceParameters.stepExponent L := by
    by_contra hn
    have hz : SourceParameters.stepExponent L = 0 := by omega
    have hb := (SourceParameters.log_step_bounds (by linarith : 0 ≤ L)).1
    simp only [SourceParameters.step, hz, pow_zero, Real.log_one] at hb
    exact (not_le_of_gt (Real.rpow_pos_of_pos (by linarith : 0 < L) _)) hb
  have hbranch : 2 ≤ 2 ^ SourceParameters.stepExponent L := by
    simpa using (pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℕ)) he)
  let R := 2 + SourceParameters.branching L ^ 2 * ∑ i, precision i
  have hsum : 0 ≤ ∑ i, precision i := Finset.sum_nonneg (fun i _ => hp i)
  have hR : 2 ≤ R := by
    dsimp only [R]
    exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) hsum)
  let g : AngularGrid := ⟨2 ^ SourceParameters.stepExponent L, hbranch, 0, R, by linarith⟩
  refine ⟨g, ?_, hR, ?_⟩
  · simp only [g, SourceParameters.step, Nat.cast_pow, Nat.cast_ofNat]
  · intro i
    change precision i * (g.branching : ℝ)^0 ≤ R / SourceParameters.branching L ^ 2
    rw [pow_zero, mul_one, le_div_iff₀ (pow_pos (SourceParameters.branching_pos L) 2)]
    have hi : precision i ≤ ∑ j, precision j :=
      Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)
    have hb := mul_le_mul_of_nonneg_right hi (sq_nonneg (SourceParameters.branching L))
    dsimp only [R]
    nlinarith

end LipschitzHilbert

end

end OAI
