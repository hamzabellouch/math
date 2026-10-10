import OAI.Combinatorics.EditApproximation.Refinement.PhysicalFamilyMemoCoarse

namespace OAI

namespace EditApproximation

section Coarse
variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P H T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (initial : PhysicalEntry M J target.length → ℕ) (hP : 0 < P)
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

/-- Source scans and a constant setup charge for each first coarse request. -/
noncomputable def physicalFamilyCoarseInputWork (bits : ℕ) (encode : Sum Key Table → ℕ)
    (root : Table) : ℝ :=
  let result := chargedRandomMemoEvaluate source target N P ell exponent H (ell ^ 80)
    T S (passes + 1) copies factor multiplier tau eta kappa delta readGroup readInteger initial
    answer bits encode root
  ∑ entry, selectionIndicator (Sum.inr (Sum.inl entry) ∈ result.freshKeys) *
    ((physicalSource source entry.1).length + 1 : ℕ)

theorem physicalFamilyCoarseQuery_input_cost_le_width (root : Table) (hroot : root.depth = J) :
    (physicalFamilyCoarseQuery source target N P H T S passes copies factor multiplier
      tau eta kappa delta draw root).cost (fun entry => (initial entry : ℚ))
      (fun entry => (physicalSource source entry.1).length + 1) ≤
    (physicalFamilyDependencyTree source target N P H T S passes copies factor multiplier
      tau eta kappa delta initial hP draw root).widthWork M source.length := by
  apply (FiniteQuery.cost_mono_weights _ _ _ _ ?_).trans
    (chargedRandomCoarseQuery_width_cost_le source target N P H T S (passes + 1) copies
      factor multiplier tau eta kappa delta readGroup readInteger answer initial
      (physicalFamilyGroup target N P ell exponent H (ell ^ 80) passes copies draw)
      (physicalFamilyInteger source target N P ell exponent H (ell ^ 80) T S passes copies
        factor multiplier tau eta kappa delta hP draw initial)
      (physicalFamilyProgram_value source target N P ell exponent H (ell ^ 80) T S passes copies
        factor multiplier tau eta kappa delta initial hP draw) root hroot)
  intro entry
  rw [physicalSource_length_eq]
  simpa only [physicalSourceInterval, Nat.add_comm] using Nat.add_le_add_right
    (sourceIntervalAt_width M source.length entry.1.1.val (Nat.pos_of_neZero M) entry.1.2) 1

theorem physicalFamilyCoarseInputWork_le (bits : ℕ) (encode : Sum Key Table → ℕ)
    (hinjective : Function.Injective encode) (hbounded : ∀ key, encode key < 2 ^ bits)
    (root : Table) (hroot : root.depth = J) :
    physicalFamilyCoarseInputWork source target N P H T S passes copies factor multiplier
      tau eta kappa delta initial draw bits encode root ≤
    ((physicalFamilyDependencyTree source target N P H T S passes copies factor multiplier
      tau eta kappa delta initial hP draw root).widthWork M source.length : ℝ) := by
  classical
  let query := physicalFamilyCoarseQuery source target N P H T S passes copies factor multiplier
    tau eta kappa delta draw root
  have hkey (entry : PhysicalEntry M J target.length) :=
    chargedRandomMemo_coarse_key source target N P ell exponent H (ell ^ 80) T S
      (passes + 1) copies factor multiplier tau eta kappa delta readGroup readInteger answer initial
      (physicalFamilyRequestValue source target N P ell exponent H (ell ^ 80) T S passes copies
        factor multiplier tau eta kappa delta initial hP draw)
      (physicalFamilyProgram_value source target N P ell exponent H (ell ^ 80) T S passes copies
        factor multiplier tau eta kappa delta initial hP draw)
      bits encode hinjective hbounded root entry
  have hs := sum_selected_nat_weights_le (query.keys (fun entry => (initial entry : ℚ)))
    (fun entry => (physicalSource source entry.1).length + 1)
  have hc := physicalFamilyCoarseQuery_input_cost_le_width source target N P H T S passes copies
    factor multiplier tau eta kappa delta initial hP draw root hroot
  change query.cost (fun entry => (initial entry : ℚ))
    (fun entry => (physicalSource source entry.1).length + 1) ≤ _ at hc
  rw [FiniteQuery.cost_eq_sum] at hc
  apply le_trans (b := ∑ entry, selectionIndicator (entry ∈ query.keys
    (fun entry => (initial entry : ℚ))) * ((physicalSource source entry.1).length + 1 : ℕ))
  · unfold physicalFamilyCoarseInputWork
    apply Finset.sum_le_sum
    intro entry _
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    by_cases he : Sum.inr (Sum.inl entry) ∈
        (chargedRandomMemoEvaluate source target N P ell exponent H (ell ^ 80) T S (passes + 1)
          copies factor multiplier tau eta kappa delta readGroup readInteger initial answer
          bits encode root).freshKeys
    · have hq := hkey entry he
      change entry ∈ query.keys (fun entry => (initial entry : ℚ)) at hq
      simp only [selectionIndicator, he, hq, ite_true, le_refl]
    · simp only [selectionIndicator, he, ite_false]
      split <;> norm_num
  · exact hs.trans (by exact_mod_cast hc)

end Coarse
end EditApproximation

end OAI
