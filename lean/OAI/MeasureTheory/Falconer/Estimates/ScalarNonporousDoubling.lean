import OAI.MeasureTheory.Falconer.Estimates.ScalarNonporousGrowth
import OAI.MeasureTheory.Falconer.Estimates.ScalarSumsetPacking

namespace OAI

/-! The nonporous alternative contradicts a small doubling bound once
 the explicit branching count exceeds the fixed-fold Pluennecke budget. -/
namespace Falconer.Regularization
open scoped Pointwise
 theorem scalar_nonporous_doubling_bound {B M copies J L C : ℕ} {U K : ℝ}
    (Q : Finset (CellPath 1)) (hQ : Q ⊆ cubePaths 1 (B*M)) (hne : Q.Nonempty)
    (branch n : ℕ → ℕ)
    (hlevel : ∀ i < M, ScalarBranchingLevel Q (B*i) (B*(i+1)) (branch i) (n i))
    (t : ℕ) (g : ℕ → ℕ) (hg : ∀ i < t, g i < g (i+1)) (hgM : ∀ i < t, g i < M)
    (hbranch : ∀ i < t, branch (g i) ≠ 0)
    (hpor : ∀ i < t, B*(g i+1) ≤ n (g i)+C)
    (hU : 18*(2:ℝ)^C ≤ U) (hJ : 0 < J)
    (hcontract : (1/2:ℝ)^B*(1+2*(J:ℝ)*U) ≤ 1)
    (hL : 4*(J:ℝ)*U ≤ (L:ℝ)) (hcopies : (2*L+1)*J ≤ copies)
    (hK : 0 ≤ K)
    (hsmall : ((scalarCells ((1/2:ℝ)^(B*M))
      (Q.image scalarPathCenter+Q.image scalarPathCenter)).card:ℝ) ≤
      K*(scalarCells ((1/2:ℝ)^(B*M)) (Q.image scalarPathCenter)).card) :
    (((J+1)^t:ℕ):ℝ) ≤ (copies+2)*(2*K)^copies*(Q.card:ℝ) := by
  obtain ⟨E,hE,hcard,hsep⟩ := scalar_nonporous_growth Q hQ hne branch n hlevel t g hg hgM
    hbranch hpor hU hJ hcontract hL hcopies
  have hA : (Q.image scalarPathCenter).Nonempty := hne.image scalarPathCenter
  have hh := scalar_separated_sumset_bound (pow_pos (by norm_num : (0:ℝ) < 1/2) (B*M))
    (Q.image scalarPathCenter) hA hsmall copies E hE hsep
  have hsize : ((scalarCells ((1/2:ℝ)^(B*M)) (Q.image scalarPathCenter)).card:ℝ) ≤ (Q.card:ℝ) := by
    exact_mod_cast (Finset.card_image_le.trans (Finset.card_image_le (s := Q)))
  rw [hcard] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hsize (by positivity))

end Falconer.Regularization

end OAI
