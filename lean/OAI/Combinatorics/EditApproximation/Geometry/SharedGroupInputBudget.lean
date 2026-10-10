import OAI.Combinatorics.EditApproximation.Geometry.ActualRoundedGroupInputs
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! A pathwise finite cover for every shared group estimator's current
child inputs. Repeated samples and member uses are counted once. -/

namespace EditApproximation

open Finset



theorem groupQueriedChildLabels_card (M Q b : ℕ) (h : ℚ)
    (draw : Fin (groupSampleCount M Q b h) → Fin M) :
    (groupQueriedChildLabels M Q b h draw).card ≤ groupSampleCount M Q b h := by
  unfold groupQueriedChildLabels
  split_ifs with hexact
  · simpa only [Finset.card_univ, Fintype.card_fin, hexact] using le_rfl (a := M)
  · exact (Finset.card_image_le).trans_eq (by simp only [Finset.card_univ, Fintype.card_fin])



theorem actual_group_input_in_cover {α : Type*} (source target : List α) {M b P exponent : ℕ}
    (parent : TargetInterval source.length) (tau a : ℚ) (F Q : ℕ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial : Fin M → TargetInterval target.length → ℚ) (cell : ℕ × ℕ)
    (member : UnskippedBand source target parent b P exponent tau F child initial)
    (hb : 1 ≤ b)
    (hcenter : member.center ∈ cellRepresentativeStates target.length P F b a parentInitial
      ((2 : ℚ) ^ (-(exponent : ℤ))) cell)
    (h : ℚ) (draw : Fin (groupSampleCount M Q b h) → Fin M)
    (i : Fin M) (hi : i ∈ groupQueriedChildLabels M Q b h draw) (henvelope : member.envelope i = h) :
    (i, member.rounded i) ∈ groupCurrentInputCover source target parent b exponent Q cell h draw := by
  apply Finset.mem_biUnion.mpr
  refine ⟨i, hi, Finset.mem_image.mpr ?_⟩
  exact ⟨member.rounded i, List.mem_toFinset.mpr
    (actual_rounded_group_input_mem source target parent tau a F parentInitial child initial cell
      member hb hcenter i h henvelope), rfl⟩

/-- One group and one envelope label use at most 624*M*Q*theta^-2
distinct current child inputs, on every seed and every sample outcome. -/
theorem groupCurrentInputCover_card {α : Type*} (source target : List α) {M b : ℕ}
    (parent : TargetInterval source.length) (exponent Q : ℕ) (cell : ℕ × ℕ) (h : ℚ)
    (hM : 0 < M) (hQ : 1 ≤ Q) (hb : 0 < b) (hh : 0 < h) (hfloor : (b : ℚ) / M ≤ h)
    (draw : Fin (groupSampleCount M Q b h) → Fin M) :
    ((groupCurrentInputCover source target parent b exponent Q cell h draw).card : ℚ) ≤
      624 * M * Q * ((2 : ℚ) ^ exponent) ^ 2 := by
  let labels := groupQueriedChildLabels M Q b h draw
  let C : ℚ := 208 * ((2 : ℚ) ^ exponent) ^ 2 * (1 + b / h)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hlength (i : Fin M) :
      ((groupRoundedStateList source target parent b exponent cell i h).length : ℚ) ≤ C :=
    groupRoundedStateList_length source target parent b exponent cell i h hh
  have hcardN : (groupCurrentInputCover source target parent b exponent Q cell h draw).card ≤
      ∑ i ∈ labels, (groupRoundedStateList source target parent b exponent cell i h).length := by
    apply Finset.card_biUnion_le.trans
    apply Finset.sum_le_sum
    intro i _
    exact Finset.card_image_le.trans (List.toFinset_card_le _)
  have hcardR : ((groupCurrentInputCover source target parent b exponent Q cell h draw).card : ℚ) ≤
      ∑ i ∈ labels, ((groupRoundedStateList source target parent b exponent cell i h).length : ℚ) := by
    exact_mod_cast hcardN
  have hlabels : (labels.card : ℚ) ≤ groupSampleCount M Q b h := by
    exact_mod_cast groupQueriedChildLabels_card M Q b h draw
  calc
    _ ≤ ∑ i ∈ labels, ((groupRoundedStateList source target parent b exponent cell i h).length : ℚ) := hcardR
    _ ≤ ∑ _i ∈ labels, C := Finset.sum_le_sum (fun i _ => hlength i)
    _ = (labels.card : ℚ) * C := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (groupSampleCount M Q b h : ℚ) * C := mul_le_mul_of_nonneg_right hlabels hC
    _ ≤ _ := shared_rounded_inputs_bound hM hQ hb hh hfloor le_rfl

end EditApproximation

end OAI
