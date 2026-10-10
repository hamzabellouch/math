import OAI.MeasureTheory.Falconer.Estimates.ScalarNonporousEntropy

namespace OAI

/-! Applying the binary sumset construction to obtain a positive
 fraction of actual porous levels in the regularized scalar tree. -/
namespace Falconer.Regularization
open scoped Pointwise

 theorem scalar_many_porous_levels {B M copies J L C : ℕ} {U K κ : ℝ}
    (Q : Finset (CellPath 1)) (hQ : Q ⊆ cubePaths 1 (B*M)) (hne : Q.Nonempty)
    (branch n : ℕ → ℕ)
    (hlevel : ∀ i < M, ScalarBranchingLevel Q (B*i) (B*(i+1)) (branch i) (n i))
    (hU : 18*(2:ℝ)^C ≤ U) (hJ : 0 < J)
    (hcontract : (1/2:ℝ)^B*(1+2*(J:ℝ)*U) ≤ 1)
    (hL : 4*(J:ℝ)*U ≤ (L:ℝ)) (hcopies : (2*L+1)*J ≤ copies)
    (hK : 0 < K)
    (hsmall : ((scalarCells ((1/2:ℝ)^(B*M))
      (Q.image scalarPathCenter+Q.image scalarPathCenter)).card:ℝ) ≤
      K*(scalarCells ((1/2:ℝ)^(B*M)) (Q.image scalarPathCenter)).card)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hB : 0 < B)
    (hlogJ : (1-κ/4)*(B:ℝ)*Real.log 2 ≤ Real.log (J+1:ℝ))
    (hcost : Real.log (copies+2:ℝ)+(copies:ℝ)*Real.log (2*K) ≤
      (κ/4)*(B:ℝ)*(M:ℝ)*Real.log 2)
    (hsize : Real.log (Q.card:ℝ) ≤ (1-κ)*(B:ℝ)*(M:ℝ)*Real.log 2) :
    (κ/2)*(M:ℝ) ≤ ((scalarPorousLevels M B C branch n).card:ℝ) := by
  have hraw := scalar_nonporous_levels_bound Q hQ hne branch n hlevel hU hJ
    hcontract hL hcopies hK.le hsmall
  have hraw' : (J+1:ℝ)^((scalarNonporousLevels M B C branch n).card) ≤
      (copies+2)*(2*K)^copies*(Q.card:ℝ) := by
    simpa only [Nat.cast_pow,Nat.cast_add,Nat.cast_one] using hraw
  have hlog := scalar_nonporous_log_bound hK hne.card_pos hraw'
  exact scalar_porous_count_from_entropy branch n hκ hκ1 hB hlogJ hcost hsize hlog

end Falconer.Regularization

end OAI
