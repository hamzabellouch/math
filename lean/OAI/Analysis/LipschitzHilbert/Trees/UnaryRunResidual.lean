import OAI.Analysis.LipschitzHilbert.Trees.UnaryRunVariation
import Mathlib.Analysis.MeanInequalities

namespace OAI

/-! The cubic residual cost over all constructed unary runs. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

theorem unary_runs_residual_sum {unary : ℕ → Prop} {n : ℕ → ℝ} {start finish : ℕ}
    (R : UnaryRunPartition unary start finish)
    (P : ∀ r : R.runs, UnarySegmentPartition n r.val.1 r.val.2)
    (hn : Antitone n) {c M μ V : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hM : 1 ≤ M) (hμ : μ ≤ 1 / 12) (hV : 0 ≤ V)
    (hmass : ∀ i : UnaryRunSegment R P, M ≤ n i.2.val.1)
    (hinterruption : ∀ j, start ≤ j → j < finish → ¬ unary j → c ≤ n j - n (j + 1))
    {E : Type*} [NormedAddCommGroup E] (F : ℕ → E)
    (level : ℕ → ℕ) (hlevel : StrictMono level) (N : ℕ) (hend : level finish ≤ N)
    (hvariation : finiteCubicVariation (fun k => F (min k N)) (2 * N) ≤ V ^ 3) :
    (∑ i : UnaryRunSegment R P, (n i.2.val.1) ^ (-1 + μ) *
      intervalOscillation F N (level i.2.val.1) (level i.2.val.2)) ≤
      (2 * (2 + 17 / c)) ^ (2 / 3 : ℝ) * M ^ (-(1 / 3 : ℝ) + μ) * V := by
  let mass : UnaryRunSegment R P → ℝ := fun i => n i.2.val.1
  let residual : UnaryRunSegment R P → ℝ := fun i =>
    intervalOscillation F N (level i.2.val.1) (level i.2.val.2)
  have hresidual (i : UnaryRunSegment R P) : 0 ≤ residual i :=
    intervalOscillation_nonneg _ _ _ _
  have hcube : ∑ i, residual i ^ 3 ≤ V ^ 3 :=
    (unary_runs_oscillation_cube_sum R P F level hlevel N hend).trans hvariation
  have hM0 : 0 < M := by linarith
  have hmass0 (i : UnaryRunSegment R P) : 0 < mass i := hM0.trans_le (hmass i)
  have hweight := unary_runs_weight_sum R P hn hc hc1 hM hμ hmass hinterruption
  have hws : (∑ i, (mass i ^ (-1 + μ)) ^ (3 / 2 : ℝ)) ≤
      2 * (2 + 17 / c) * M ^ (-(1 / 2 : ℝ) + 3 * μ / 2) := by
    convert hweight using 1
    apply Finset.sum_congr rfl
    intro i _
    rw [← Real.rpow_mul (hmass0 i).le]
  have hweightRoot : (∑ i, (mass i ^ (-1 + μ)) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) ≤
      (2 * (2 + 17 / c)) ^ (2 / 3 : ℝ) * M ^ (-(1 / 3 : ℝ) + μ) := by
    apply (Real.rpow_le_rpow
      (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (Real.rpow_nonneg (hmass0 i).le _) _)
      hws (by norm_num : (0 : ℝ) ≤ 2 / 3)).trans_eq
    rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hM0.le _), ← Real.rpow_mul hM0.le]
    congr 2
    ring
  have hresidualRoot : (∑ i, residual i ^ (3 : ℝ)) ^ (1 / 3 : ℝ) ≤ V := by
    have hcube' : (∑ i, residual i ^ (3 : ℝ)) ≤ V ^ (3 : ℝ) := by
      convert hcube using 1
      · apply Finset.sum_congr rfl
        intro i _
        exact Real.rpow_natCast _ 3
      · exact Real.rpow_natCast _ 3
    apply (Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hresidual i) _)
      hcube' (by norm_num : (0 : ℝ) ≤ 1 / 3)).trans_eq
    rw [← Real.rpow_mul hV]
    norm_num
  have hholder := Real.inner_le_Lp_mul_Lq_of_nonneg Finset.univ
    (f := fun i => mass i ^ (-1 + μ)) (g := residual)
    (show Real.HolderConjugate (3 / 2 : ℝ) 3 by norm_num [Real.holderConjugate_iff])
    (fun i _ => Real.rpow_nonneg (hmass0 i).le _) (fun i _ => hresidual i)
  norm_num only [one_div_div, div_one] at hholder
  exact hholder.trans (mul_le_mul hweightRoot hresidualRoot
    (Real.rpow_nonneg (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hresidual i) _) _)
    (mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hM0.le _)))

end LipschitzHilbert

end

end OAI
