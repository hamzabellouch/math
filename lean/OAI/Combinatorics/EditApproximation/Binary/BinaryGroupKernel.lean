import OAI.Combinatorics.EditApproximation.Binary.BinaryBellmanKernel
import OAI.Combinatorics.EditApproximation.Geometry.BandGroupSampling
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Literal group estimates on gathered stored fractions. Each child/scale
comparison is executed, the supplied draw indices are reused, and ordered
selection uses the same tie rule as the mathematical group program. -/

namespace EditApproximation
namespace BinaryFraction

open Finset



@[simp] theorem equalWithWork_value (a b : BinaryFraction) :
    (equalWithWork a b).1 = true ↔ a.value = b.value := by
  simp only [equalWithWork, Bool.and_eq_true, leWithWork_value]
  exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩

theorem equalWithWork_cost (a b : BinaryFraction) (B : ℕ) (ha : a.width ≤ B) (hb : b.width ≤ B) :
    (equalWithWork a b).2 ≤ 2 * (1000 * (B + 1) ^ 2 + 1) + 1 := by
  have hl := leWithWork_cost a b B ha hb
  have hr := leWithWork_cost b a B hb ha
  change _ + _ + 1 ≤ _
  omega



@[simp] theorem groupTermsWithWork_value {M : ℕ} (h : BinaryFraction)
    (envelope values : Vector BinaryFraction M) (indices : List (Fin M)) :
    ((groupTermsWithWork h envelope values indices).1.map value) =
      indices.map (fun i => if (envelope.get i).value = h.value then (values.get i).value else 0) := by
  simp only [groupTermsWithWork, arithmeticMapWithWork_value, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro i _
  by_cases hi : (envelope.get i).value = h.value
  · have ht := (equalWithWork_value (envelope.get i) h).mpr hi
    simp only [ht, ↓reduceIte, hi]
  · have ht : (equalWithWork (envelope.get i) h).1 = false :=
      Bool.eq_false_iff.mpr (fun h => hi ((equalWithWork_value _ _).mp h))
    simp only [ht, Bool.false_eq_true, ↓reduceIte, hi]
    rw [← representation_value, zero_representation, UnreducedRational.value_zero]



@[simp] theorem groupIndexWithWork_value {M : ℕ} (h : BinaryFraction)
    (envelope values : Vector BinaryFraction M) (indices : List (Fin M)) :
    (groupIndexWithWork h envelope values indices).1.value =
      (indices.map fun i => if (envelope.get i).value = h.value then (values.get i).value else 0).sum := by
  simp only [groupIndexWithWork, sumListWithWork_value, groupTermsWithWork_value]

def groupIndexBitBudget (n B : ℕ) : ℕ :=
  n * (2 * (1000 * (B + 1) ^ 2 + 1) + 6) + storedSumBitBudget n B + 6 * n + 1

theorem groupIndexWithWork_bounds {M : ℕ} (h : BinaryFraction)
    (envelope values : Vector BinaryFraction M) (indices : List (Fin M)) (B : ℕ)
    (hB : 1 ≤ B) (hh : h.width ≤ B) (he : ∀ i, (envelope.get i).width ≤ B)
    (hv : ∀ i, (values.get i).width ≤ B) :
    (groupIndexWithWork h envelope values indices).1.width ≤ bandMassTotalStorageBudget indices.length B ∧
    (groupIndexWithWork h envelope values indices).2 ≤ groupIndexBitBudget indices.length B := by
  have hwidth : ∀ a ∈ (groupTermsWithWork h envelope values indices).1, a.width ≤ B := by
    intro a ha
    simp only [groupTermsWithWork, arithmeticMapWithWork_value] at ha
    obtain ⟨i, _, heq⟩ := List.mem_map.mp ha
    subst a
    split_ifs
    · exact hv i
    · exact hB
  have hlen : (groupTermsWithWork h envelope values indices).1.length = indices.length := by
    simp only [groupTermsWithWork, arithmeticMapWithWork_value, List.length_map]
  have hw := sumListWithWork_width _ B hwidth
  have hc := sumListWithWork_cost _ B hwidth
  rw [hlen] at hw hc
  have ht : (groupTermsWithWork h envelope values indices).2 ≤
      indices.length * (2 * (1000 * (B + 1) ^ 2 + 1) + 6) := by
    apply arithmeticMapWithWork_cost
    intro i _
    have h := equalWithWork_cost (envelope.get i) h B (he i) hh
    change _ + 2 ≤ _
    omega
  refine ⟨hw, ?_⟩
  change _ + _ + 1 ≤ _
  unfold groupIndexBitBudget
  omega

def groupScaleWithWork {M : ℕ} (k : ℕ) (h : BinaryFraction)
    (envelope values : Vector BinaryFraction M) (draw : Fin k → Fin M) : BinaryFraction × ℕ :=
  let indices := if k = M then List.finRange M else (List.finRange k).map draw
  let subtotal := groupIndexWithWork h envelope values indices
  let factor := if k = M then (one, 1) else divWithWork (nat M) (nat k)
  let result := canonicalMulWithWork factor.1 subtotal.1
  (result.1, subtotal.2 + factor.2 + result.2 + Nat.size M + Nat.size k + 3)

@[simp] theorem groupScaleWithWork_value {M : ℕ} (k : ℕ) (h : BinaryFraction)
    (envelope values : Vector BinaryFraction M) (draw : Fin k → Fin M) :
    (groupScaleWithWork k h envelope values draw).1.value =
      groupScaleEstimate k h.value (fun i => (envelope.get i).value) (fun i => (values.get i).value) draw := by
  unfold groupScaleWithWork groupScaleEstimate
  split_ifs with heq
  · simp only [canonicalMulWithWork_value, groupIndexWithWork_value, one, nat_value, Nat.cast_one, one_mul]
    simp only [groupScaleTrueCost, ← List.ofFn_eq_map, List.sum_ofFn]
  · simp only [canonicalMulWithWork_value, groupIndexWithWork_value, divWithWork_value, nat_value,
      List.map_map, Function.comp_def]
    rw [← List.ofFn_eq_map, List.sum_ofFn]

def groupScaleTermCount (M k : ℕ) : ℕ := if k = M then M else k

def groupScaleWordBudget (M k B : ℕ) : ℕ :=
  4 * (4 * B + 4 + bandMassTotalStorageBudget (groupScaleTermCount M k) B) + 2

def groupScaleBitBudget (M k B : ℕ) : ℕ :=
  groupIndexBitBudget (groupScaleTermCount M k) B + (2100 * (B + 2) ^ 2 + 1) +
    2000 * (4 * B + 4 + bandMassTotalStorageBudget (groupScaleTermCount M k) B + 1) ^ 2 + 2 * B + 3

theorem groupScaleWithWork_bounds {M : ℕ} (k : ℕ) (h : BinaryFraction)
    (envelope values : Vector BinaryFraction M) (draw : Fin k → Fin M) (B : ℕ)
    (hB : 1 ≤ B) (hh : h.width ≤ B) (he : ∀ i, (envelope.get i).width ≤ B)
    (hv : ∀ i, (values.get i).width ≤ B) (hM : Nat.size M + 2 ≤ B) (hk : Nat.size k + 2 ≤ B) :
    (groupScaleWithWork k h envelope values draw).1.width ≤ groupScaleWordBudget M k B ∧
    (groupScaleWithWork k h envelope values draw).2 ≤ groupScaleBitBudget M k B := by
  let indices := if k = M then List.finRange M else (List.finRange k).map draw
  let factor : BinaryFraction × ℕ := if k = M then (one, 1) else divWithWork (nat M) (nat k)
  have hlen : indices.length = groupScaleTermCount M k := by
    dsimp only [indices, groupScaleTermCount]
    split_ifs <;> simp only [List.length_finRange, List.length_map]
  obtain ⟨hsw, hsc⟩ := groupIndexWithWork_bounds h envelope values indices B hB hh he hv
  rw [hlen] at hsw hsc
  have hfw : factor.1.width ≤ 4 * B + 4 := by
    dsimp only [factor]
    split_ifs
    · change 1 ≤ 4 * B + 4
      omega
    · exact divWithWork_width_uniform _ _ B ((nat_width_le _).trans hM) ((nat_width_le _).trans hk)
  have hfc : factor.2 ≤ 2100 * (B + 2) ^ 2 + 1 := by
    dsimp only [factor]
    split_ifs
    · omega
    · exact (divWithWork_cost _ _ B ((nat_width_le _).trans hM)
        ((nat_width_le _).trans hk)).trans (Nat.le_succ _)
  have hrw := canonicalMulWithWork_width factor.1 (groupIndexWithWork h envelope values indices).1
    (4 * B + 4 + bandMassTotalStorageBudget (groupScaleTermCount M k) B) (by omega) (by omega)
  have hrc := canonicalMulWithWork_cost factor.1 (groupIndexWithWork h envelope values indices).1
    (4 * B + 4 + bandMassTotalStorageBudget (groupScaleTermCount M k) B) (by omega) (by omega)
  refine ⟨hrw, ?_⟩
  change (groupIndexWithWork h envelope values indices).2 + factor.2 +
    (canonicalMulWithWork factor.1 (groupIndexWithWork h envelope values indices).1).2 +
      Nat.size M + Nat.size k + 3 ≤ _
  unfold groupScaleBitBudget
  omega

/-- Every scale is accumulated using the same finite child arrays. -/
def groupMemberWithWork {M T : ℕ} (scales : Fin T → BinaryFraction) (count : Fin T → ℕ)
    (connection : BinaryFraction) (envelope values : Vector BinaryFraction M)
    (draw : ∀ s : Fin T, Fin (count s) → Fin M) : BinaryFraction × ℕ :=
  let terms := arithmeticMapWithWork (fun s => groupScaleWithWork (count s) (scales s)
    envelope values (draw s)) (List.finRange T)
  let subtotal := sumListWithWork terms.1
  let result := canonicalAddWithWork connection subtotal.1
  (result.1, terms.2 + subtotal.2 + result.2 + 1)

@[simp] theorem groupMemberWithWork_value {M T : ℕ} (scales : Fin T → BinaryFraction)
    (count : Fin T → ℕ) (connection : BinaryFraction) (envelope values : Vector BinaryFraction M)
    (draw : ∀ s : Fin T, Fin (count s) → Fin M) :
    (groupMemberWithWork scales count connection envelope values draw).1.value =
      groupMemberEstimate (fun s => (scales s).value) count connection.value
        (fun i => (envelope.get i).value) (fun i => (values.get i).value) draw := by
  simp only [groupMemberWithWork, canonicalAddWithWork_value, sumListWithWork_value,
    arithmeticMapWithWork_value, List.map_map, Function.comp_def, groupScaleWithWork_value,
    groupMemberEstimate]
  rw [← List.ofFn_eq_map, List.sum_ofFn]

def groupMemberWordBudget (T B W : ℕ) : ℕ :=
  8 * (B + bandMassTotalStorageBudget T W) + 6

def groupMemberBitBudget (T B C W : ℕ) : ℕ :=
  T * (C + 3) + storedSumBitBudget T W + 6 * T +
    6000 * (B + bandMassTotalStorageBudget T W + 1) ^ 2 + 1

theorem groupMemberWithWork_bounds {M T : ℕ} (scales : Fin T → BinaryFraction)
    (count : Fin T → ℕ) (connection : BinaryFraction) (envelope values : Vector BinaryFraction M)
    (draw : ∀ s : Fin T, Fin (count s) → Fin M) (B C W : ℕ)
    (hb : connection.width ≤ B)
    (hc : ∀ s, (groupScaleWithWork (count s) (scales s) envelope values (draw s)).2 ≤ C)
    (hw : ∀ s, (groupScaleWithWork (count s) (scales s) envelope values (draw s)).1.width ≤ W) :
    (groupMemberWithWork scales count connection envelope values draw).1.width ≤ groupMemberWordBudget T B W ∧
    (groupMemberWithWork scales count connection envelope values draw).2 ≤ groupMemberBitBudget T B C W := by
  let terms := arithmeticMapWithWork (fun s => groupScaleWithWork (count s) (scales s)
    envelope values (draw s)) (List.finRange T)
  have hlen : terms.1.length = T := by
    simp only [terms, arithmeticMapWithWork_value, List.length_map, List.length_finRange]
  have hterms : ∀ a ∈ terms.1, a.width ≤ W := by
    intro a ha
    simp only [terms, arithmeticMapWithWork_value] at ha
    obtain ⟨s, _, heq⟩ := List.mem_map.mp ha
    subst a
    exact hw s
  have htw := sumListWithWork_width terms.1 W hterms
  have htc := sumListWithWork_cost terms.1 W hterms
  rw [hlen] at htw htc
  have hmc := arithmeticMapWithWork_cost (fun s => groupScaleWithWork (count s) (scales s)
    envelope values (draw s)) (List.finRange T) C (fun s _ => hc s)
  simp only [List.length_finRange] at hmc
  have hrw := canonicalAddWithWork_width connection (sumListWithWork terms.1).1
    (B + bandMassTotalStorageBudget T W) (by omega) (by omega)
  have hrc := canonicalAddWithWork_cost connection (sumListWithWork terms.1).1
    (B + bandMassTotalStorageBudget T W) (by omega) (by omega)
  refine ⟨hrw, ?_⟩
  change terms.2 + (sumListWithWork terms.1).2 + (canonicalAddWithWork connection
    (sumListWithWork terms.1).1).2 + 1 ≤ _
  unfold groupMemberBitBudget
  change terms.2 ≤ T * (C + 3) at hmc
  omega



@[simp] theorem selectGroupWithWork_value {ι : Type*} (members : List ι) (hne : members ≠ [])
    (estimate : ι → BinaryFraction × ℕ) :
    (selectGroupWithWork members hne estimate).1 =
      selectGroupMember members hne (fun member => (estimate member).1.value) := by
  simp only [selectGroupWithWork, scoredArgmaxWithWork_value, neg_value,
    Option.map_map, Function.comp_def, selectGroupMember]
  congr 1
  cases members.argmax (fun member => -(estimate member).1.value) <;> rfl

theorem selectGroupWithWork_cost {ι : Type*} (members : List ι) (hne : members ≠ [])
    (estimate : ι → BinaryFraction × ℕ) (C W : ℕ)
    (hc : ∀ member ∈ members, (estimate member).2 ≤ C)
    (hw : ∀ member ∈ members, (estimate member).1.width ≤ W) :
    (selectGroupWithWork members hne estimate).2 ≤
      members.length * (C + 1000 * (W + 1) ^ 2 + 3) + 1 := by
  have h := scoredArgmaxWithWork_cost (fun member => ((estimate member).1.neg, (estimate member).2 + 1))
    members (C + 1) W (by intro member hm; have := hc member hm; omega)
    (by intro member hm; simpa only [neg_width] using hw member hm)
  change _ + 1 ≤ _
  have heq : (C + 1) + 1000 * (W + 1) ^ 2 + 2 = C + 1000 * (W + 1) ^ 2 + 3 := by omega
  rw [heq] at h
  exact Nat.add_le_add_right h 1

end BinaryFraction
end EditApproximation

end OAI
