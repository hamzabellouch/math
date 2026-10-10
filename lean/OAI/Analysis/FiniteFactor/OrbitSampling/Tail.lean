import OAI.Analysis.FiniteFactor.CrossedProduct.StageOperator

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped ENNReal Topology
noncomputable section

theorem sourceCutoff_ge_shift (s n : ℕ) :
    2^n * (sourceStageState s).K ≤ (sourceStageState (s+n)).K := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hh := sourceStage_cutoff_growth (s+n)
    rw [pow_succ, Nat.add_succ]
    nlinarith

/-- The exact geometric tail estimate used in scales and tail trimming. -/
theorem sourceCutoff_tail_bound (s : ℕ) :
    (∑' n : ℕ, 1 / ((sourceStageState (s+n)).K : ℝ)) ≤
      2 / ((sourceStageState s).K : ℝ) := by
  let b (n : ℕ) : ℝ := (1 / ((sourceStageState s).K : ℝ)) * (1/2 : ℝ)^n
  have hb : Summable b := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) < 1)).mul_left _
  have hle (n : ℕ) : 1 / ((sourceStageState (s+n)).K : ℝ) ≤ b n := by
    have hh : (2 : ℝ)^n * (sourceStageState s).K ≤ (sourceStageState (s+n)).K :=
      by exact_mod_cast sourceCutoff_ge_shift s n
    have hp : (0 : ℝ) < 2^n * (sourceStageState s).K := mul_pos (by positivity) (sourceCutoff_pos s)
    have ht := one_div_le_one_div_of_le hp hh
    simpa [b, one_div_pow, mul_comm, mul_left_comm] using ht
  calc
    _ ≤ ∑' n, b n := (hb.of_nonneg_of_le (fun _ => by positivity) hle).tsum_le_tsum hle hb
    _ = 2 / ((sourceStageState s).K : ℝ) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num)]
      ring

def sourceTailAngleSum (θ : SourceCoordinate → ℝ) (s : ℕ) : ℝ :=
  ∑' n : ℕ, ∑ i : Fin (sourceBlockSize (s+n)), θ ⟨s+n,i⟩

theorem SourceAngles.tail_sum_bound {θ : SourceCoordinate → ℝ} (hθ : SourceAngles θ) (s : ℕ) :
    sourceTailAngleSum θ s ≤ 4 / ((sourceStageState s).K : ℝ) := by
  have hb (n : ℕ) :
      (∑ i : Fin (sourceBlockSize (s+n)), θ ⟨s+n,i⟩) ≤ 2 / ((sourceStageState (s+n)).K : ℝ) := by
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (hθ ⟨s+n,i⟩).2)
    have he : (∑ _i : Fin (sourceBlockSize (s+n)),
        2 / ((sourceBlockSize (s+n) : ℝ)*(sourceStageState (s+n)).K)) =
        2 / ((sourceStageState (s+n)).K : ℝ) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp [(sourceBlockSize_pos (s+n)).ne', (sourceCutoff_pos (s+n)).ne']
    exact hh.trans_eq he
  have hs : Summable (fun n => 2 / ((sourceStageState (s+n)).K : ℝ)) := by
    have hh := sourceCutoff_reciprocal_summable.comp_injective (add_right_injective s)
    simpa [div_eq_mul_inv] using hh.mul_left 2
  calc
    sourceTailAngleSum θ s ≤ ∑' n, 2 / ((sourceStageState (s+n)).K : ℝ) :=
      (hs.of_nonneg_of_le (fun n => Finset.sum_nonneg (fun i _ => hθ.nonneg _)) hb).tsum_le_tsum hb hs
    _ = 2 * ∑' n, 1 / ((sourceStageState (s+n)).K : ℝ) := by
      rw [← tsum_mul_left]; congr; funext n; ring
    _ ≤ 2 * (2 / ((sourceStageState s).K : ℝ)) :=
      mul_le_mul_of_nonneg_left (sourceCutoff_tail_bound s) (by norm_num)
    _ = 4 / ((sourceStageState s).K : ℝ) := by ring

/-- The largest proposed sampling power divided by the next cutoff has the
source exponent gap 7/10 - 3/4 = -1/20. -/
theorem sourceSampling_tail_ratio (s : ℕ) :
    4 * (sourceBlockSize s : ℝ)^((7/10 : ℝ)*(sourceBlockSize s : ℝ)) /
      ((sourceStageState (s+1)).K : ℝ) ≤
    4 * (sourceBlockSize s : ℝ)^(-(sourceBlockSize s : ℝ)/20) := by
  have hm := sourceBlockSize_pos s
  have hK := sourceCutoff_pos (s+1)
  have hc : (sourceBlockSize s : ℝ)^((3/4 : ℝ)*(sourceBlockSize s : ℝ)) ≤
      (sourceStageState (s+1)).K := Nat.le_ceil _
  apply (div_le_iff₀ hK).mpr
  calc
    _ = (4 * (sourceBlockSize s : ℝ)^(-(sourceBlockSize s : ℝ)/20)) *
        (sourceBlockSize s : ℝ)^((3/4 : ℝ)*(sourceBlockSize s : ℝ)) := by
      rw [mul_assoc, ← Real.rpow_add hm]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hc (by positivity)

end
end FiniteFactor

end OAI
