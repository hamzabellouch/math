import OAI.Combinatorics.EditApproximation.Coarse.CoarseInputPreparation
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalCoarseInputWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation



theorem physicalCoarsePreparationCost_bound {M J : ℕ} (source target : List ℕ) (H : ℕ)
    (hH : 100 ≤ H) (hs : Nat.size source.length ≤ H ^ 3) (ht : Nat.size target.length ≤ H ^ 3)
    (hsymbol : ∀ a ∈ source ++ target, Nat.size a ≤ H ^ 3)
    (entry : PhysicalEntry M J target.length) :
    physicalCoarsePreparationCost source target entry ≤ H ^ 6 * ((physicalSource source entry.1).length + 1) := by
  unfold physicalCoarsePreparationCost
  rw [physicalSource_length_eq]
  exact coarsePreparedSlicesWithWork_height_bound source target
    (physicalSourceInterval source.length entry.1).lo (physicalSourceInterval source.length entry.1).hi
    entry.2.lo entry.2.hi H (physicalSourceInterval source.length entry.1).ordered
    (physicalSourceInterval source.length entry.1).valid entry.2.ordered entry.2.valid hH hs ht hsymbol

section Coarse
variable {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List ℕ) (N P H T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (initial : PhysicalEntry M J target.length → ℕ)
  (draw : PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
    target N P (inputSmallLog N) (40 * smallLogExponent N) H (inputSmallLog N ^ 80) passes copies)

local notation "ell" => inputSmallLog N
local notation "exponent" => (40 * smallLogExponent N : ℕ)
local notation "Key" => PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies
local notation "Table" => ChargedPhysicalRequest M J target.length (passes + 1) copies T S
local notation "readGroup" => physicalFamilyGroupRead (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies
local notation "readInteger" => physicalFamilyOnlineRead (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies
local notation "answer" => physicalFamilyAnswer target N P ell exponent H (ell ^ 80) passes copies draw



theorem physicalFamilyCoarsePreparationWork_bound (bits : ℕ) (encode : Sum Key Table → ℕ)
    (root : Table) (hH : 100 ≤ H) (hs : Nat.size source.length ≤ H ^ 3)
    (ht : Nat.size target.length ≤ H ^ 3)
    (hsymbol : ∀ a ∈ source ++ target, Nat.size a ≤ H ^ 3) :
    physicalFamilyCoarsePreparationWork source target N P H T S passes copies factor multiplier
      tau eta kappa delta initial draw bits encode root ≤
      (H : ℝ) ^ 6 * physicalFamilyCoarseInputWork source target N P H T S passes copies factor multiplier
        tau eta kappa delta initial draw bits encode root := by
  classical
  unfold physicalFamilyCoarsePreparationWork physicalFamilyCoarseInputWork
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro entry _
  have hc : (physicalCoarsePreparationCost source target entry : ℝ) ≤
      (H : ℝ) ^ 6 * ((physicalSource source entry.1).length + 1 : ℕ) := by
    exact_mod_cast physicalCoarsePreparationCost_bound source target H hH hs ht hsymbol entry
  have hp := mul_le_mul_of_nonneg_left hc
    (show 0 ≤ selectionIndicator (Sum.inr (Sum.inl entry) ∈
      (chargedRandomMemoEvaluate source target N P ell exponent H (ell ^ 80) T S (passes + 1)
        copies factor multiplier tau eta kappa delta readGroup readInteger initial answer bits encode root).freshKeys) by
      unfold selectionIndicator; split <;> norm_num)
  exact hp.trans_eq (by ring)

end Coarse
end EditApproximation

end OAI
