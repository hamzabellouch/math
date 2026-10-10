import OAI.NumberTheory.JointDickman.Amplification.SingularSeries

namespace OAI

/-! # A lag-independent error for the truncated singular series -/

namespace JointDickman
open Finset Filter
open scoped Topology

noncomputable def singularSeriesTail (Q : ℕ) : ℝ :=
  ∑' k : ℕ, 1/((k+Q).totient : ℝ)^2

theorem singularSeriesTail_nonneg (Q : ℕ) : 0 ≤ singularSeriesTail Q :=
  tsum_nonneg (fun _ => by positivity)

theorem singularSeriesTail_tendsto_zero :
    Tendsto singularSeriesTail atTop (𝓝 0) :=
  tendsto_sum_nat_add (fun q : ℕ => 1/(q.totient : ℝ)^2)

theorem singularSeries_tail_bound (hMP : PublishedInputs.PrimeProductMertensInput)
    (j Q : ℕ) :
    ‖(∑' q, singularSeriesCoefficient j q) - ∑ q ∈ range Q, singularSeriesCoefficient j q‖ ≤
      singularSeriesTail Q := by
  have hnorm := singularSeriesCoefficient_summable hMP j
  have hsum := hnorm.of_norm
  have hnQ : Summable (fun k => ‖singularSeriesCoefficient j (k+Q)‖) :=
    hnorm.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hmQ : Summable (fun k : ℕ => 1/((k+Q).totient : ℝ)^2) :=
    (summable_totient_reciprocal_sq hMP).comp_injective (fun _ _ h => Nat.add_right_cancel h)
  rw [← hsum.sum_add_tsum_nat_add Q,add_sub_cancel_left]
  exact (norm_tsum_le_tsum_norm hnQ).trans
    (hnQ.tsum_le_tsum (fun k => singularSeriesCoefficient_norm_le j (k+Q)) hmQ)

theorem weighted_ramanujan_residue_factor {j q : ℕ} [NeZero j] [NeZero q] [NeZero (j*q)] :
    (ArithmeticFunction.moebius q : ℝ)/(q.totient : ℝ) *
      (∑ h : ZMod (j*q), if h.val.Coprime q then
        ‖ramanujanSum (j*q) h‖^2 / ((j*q).totient : ℝ)^2 else 0) =
      ((j : ℝ)/j.totient)*singularSeriesCoefficient j q := by
  classical
  by_cases hq : Squarefree q
  · rw [ramanujan_residue_factor hq]
    by_cases hcop : j.Coprime q
    · rw [ite_eq_left hcop,singularSeriesCoefficient,ite_eq_left hcop.symm]
      ring
    · have hcop' : ¬q.Coprime j := fun h => hcop h.symm
      simp [hcop,hcop',singularSeriesCoefficient]
  · have hm := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hq
    simp [hm,singularSeriesCoefficient]

end JointDickman

end OAI
