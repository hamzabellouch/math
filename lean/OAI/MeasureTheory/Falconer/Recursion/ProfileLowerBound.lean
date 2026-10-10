import OAI.MeasureTheory.Falconer.Recursion.ProfileBranchCounts
import OAI.MeasureTheory.Falconer.Recursion.ProfileBetweenNodes

namespace OAI

/-! Convert the actual finite block-count bounds into a lower bound for the
whole normalized branching profile, including between the block depths. -/
namespace Falconer.Regularization
variable {d : ℕ}

theorem regularizedProfile_lower_from_ratios {N : ℕ} (hN : 0 < N)
    {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N) (F : CellPath d → List ℕ)
    {B : ℕ} (hB : 0 < B) (p : CellPath d) {t A : ℝ}
    (hbound : ∀ i ≤ N/B+1,
      (blockProduct L F N B i p : ℝ)/(blockProduct L F N B (N/B+1) p : ℝ) ≤
        (2 : ℝ)^(A-t*(blockDepth N B i : ℝ)))
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    t*x-A/(N : ℝ) ≤ regularizedProfile L F N B (N/B+1) p ((N : ℝ)*x) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hnodes : ∀ i ≤ N/B+1, (t/(N : ℝ))*(blockDepth N B i : ℝ)-A/(N : ℝ) ≤
      regularizedProfile L F N B (N/B+1) p (blockDepth N B i) := by
    intro i hi
    have hb := regularizedProfile_lower_of_ratio_bound hN hL F hB p hi (hbound i hi)
    rw [show (t/(N : ℝ))*(blockDepth N B i : ℝ)-A/(N : ℝ) =
        (t*(blockDepth N B i : ℝ)-A)/(N : ℝ) by ring]
    apply (div_le_iff₀ hNR).2
    nlinarith
  have hbetween : (blockDepth N B (N/B+1) : ℝ) ≤ (N : ℝ)*x ∧
      (N : ℝ)*x ≤ (blockDepth N B 0 : ℝ) := by
    simp only [blockDepth_terminal N hB,Nat.cast_zero,blockDepth,Nat.zero_mul,Nat.sub_zero]
    constructor
    · exact mul_nonneg hNR.le hx.1
    · nlinarith [mul_le_mul_of_nonneg_left hx.2 hNR.le]
  have hp := finiteRampProfile_lower_between_nodes
    (fun i => (blockDepth N B i : ℝ)) (fun i => blockSlope L F N B i p) (N/B+1)
    (fun _ _ h => Nat.cast_le.mpr (blockDepth_antitone N B h)) hnodes hbetween
  have he : (t/(N : ℝ))*((N : ℝ)*x)-A/(N : ℝ) = t*x-A/(N : ℝ) := by
    field_simp
  change t*x-A/(N : ℝ) ≤ finiteRampProfile _ _ _ _
  rw [← he]
  exact hp

end Falconer.Regularization

end OAI
