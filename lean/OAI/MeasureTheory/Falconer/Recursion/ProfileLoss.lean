import OAI.MeasureTheory.Falconer.Recursion.BranchLedger

namespace OAI

/-! # Ambient-dimensional losses in the scalar branch ledger

The policy parameter remains sigma. Only the numerical loss parameter is
enlarged, so the branch schedule and its retained descriptor lists do not change.
-/

namespace Falconer
open PlanarFalconer

noncomputable def profileLossParameter (d : ℕ) (lam σ : ℝ) : ℝ :=
  ((d:ℝ)+1)*(lam+σ)

theorem profileLossParameter_nonneg (d : ℕ) {lam σ : ℝ}
    (hlam : 0 ≤ lam) (hσ : 0 ≤ σ) : 0 ≤ profileLossParameter d lam σ := by
  unfold profileLossParameter
  positivity

theorem profile_graph_loss_le (d : ℕ) {lam σ : ℝ}
    (hlam : 0 ≤ lam) (hσ : 0 ≤ σ) :
    (1000*((d:ℝ)+1)+32*d)*σ+4*((d:ℝ)+1)*lam ≤
      4000*(profileLossParameter d lam σ+σ) := by
  unfold profileLossParameter
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) d) hlam,
    mul_nonneg (Nat.cast_nonneg (α := ℝ) d) hσ]

theorem profile_source_branch_exponent {A : ℕ → ℝ} {N n d : ℕ} {lam σ κ η : ℝ}
    (hN : 0 < N) (hlam : 0 ≤ lam) (hσ : 0 < σ) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hη : 0 < η)
    (hceil : ⌈10*σ*(N:ℝ)⌉₊ < sourcePolicyBlock N κ)
    (hslack : σ*(N:ℝ) ≤ sourcePolicyBlock N κ)
    (hlip : ∀ i j, i ≤ N → j ≤ N → |A i-A j| ≤ (d:ℝ)*|(i:ℝ)-j|/N)
    (b : PolicyBranch A N (sourcePolicyBlock N κ) σ n)
    (hinit : (b.state 0).start+10*sourcePolicyBlock N κ ≤ (b.state 0).finish) :
    ∑ j ∈ Finset.range n,
      branchExponent A (profileLossParameter d lam σ) σ (η/(2*(1+20/κ+1/σ)))
        (b.state j) (b.label j) (b.state (j+1)) ≤
      2*A (b.state 0).start-
        potential A (b.state 0).start (b.state 0).finish (10*sourcePolicyBlock N κ)+
        20*(d:ℝ)*(sourcePolicyBlock N κ:ℝ)/N+
        80000*(profileLossParameter d lam σ+σ)/κ+η/2 :=
  dimension_source_branch_exponent hN (profileLossParameter_nonneg d hlam hσ.le)
    hσ hκ hκ1 hη (Nat.cast_nonneg d) hceil hslack hlip b hinit

end Falconer

end OAI
