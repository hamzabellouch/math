import OAI.Combinatorics.EditApproximation.Coarse.CoarseAccessControlSpace
import OAI.Combinatorics.EditApproximation.Coarse.CoarseChildControlSpace
import OAI.Combinatorics.EditApproximation.Coarse.CoarseIndexedExecution

namespace OAI

namespace EditApproximation
namespace BinaryFraction

/-- Conservative recursive invocation count for the indexed evaluator,
including scalar callees, index traversals and repeated descriptor reads. -/
def coarseIndexedInvocations {B : ℕ} (k q L n : ℕ) (source target : List ℕ)
    (two : BinaryFraction) : (d offset : ℕ) → CoarseThresholdDraws B d →
    BinaryFraction → ℕ → ℕ
  | 0, offset, _, allowance, start =>
    let descriptor := coarseDescriptorWithWork B 0 n offset
    let size := bitWordValue descriptor.1
    let prune := leWithWork (nat size) allowance
    let setup := coarseDescriptorInvocations B 0 n offset + compareInvocations allowance (nat size) + 2
    if prune.1 then setup else
      let letter := coarsePaddedReadWithWork n source offset
      setup + coarsePaddedReadInvocations n offset +
        arithmeticMapInvocations (fun shift : Fin (2 * k + 1) =>
          let mismatch := coarseReadShiftWithWork k n target letter.1 start shift
          coarseReadShiftInvocations k n target letter.1 start shift +
            coarseGridNatInvocations allowance.denominator allowance.denominator_pos mismatch.1 + 1)
          (List.finRange (2 * k + 1)) + (2 * k + 1) + 1
  | d + 1, offset, (draws, below), allowance, start =>
    let descriptor := coarseDescriptorWithWork B (d + 1) n offset
    let size := bitWordValue descriptor.1
    let prune := leWithWork (nat size) allowance
    let setup := coarseDescriptorInvocations B (d + 1) n offset + compareInvocations allowance (nat size) + 2
    if prune.1 then setup else
      let capacity := bitPowerWithWork B.bits d
      let childOffset := fun i : Fin B =>
        coarseChildOffsetWithWork offset (bitWordValue capacity.1) i.val
      let childSize := fun i : Fin B =>
        coarseDescriptorWithWork B d n (bitWordValue (childOffset i).1)
      let evaluate := fun (i : Fin B) a s =>
        let evaluated := coarseIndexedWithWork k q L n source target two d
          (bitWordValue (childOffset i).1) (below i) a s
        let next := binaryNaturalAddWithWork s (bitWordValue (childSize i).1)
        (evaluated.1, evaluated.2 + 3 * ((childOffset i).2 + (childSize i).2 + next.2 + 3))
      let allocation := fun (i : Fin B) a s =>
        coarseIndexedInvocations k q L n source target two d
          (bitWordValue (childOffset i).1) (below i) a s +
          3 * (coarseChildOffsetInvocations offset (bitWordValue capacity.1) i.val +
            coarseDescriptorInvocations B d n (bitWordValue (childOffset i).1) +
            bitAddInvocations s.bits (bitWordValue (childSize i).1).bits false) + 1
      setup + bitPowerInvocations B.bits d +
        coarseIndexChildrenInvocations q L two (fun i => bitWordValue (childSize i).1)
          evaluate allocation draws allowance (List.finRange B) start + B + 1

theorem arithmeticMapInvocations_with_indices_le_work {α β : Type*} (f : α → β × ℕ)
    (invocations : α → ℕ) (values : List α)
    (h : ∀ a ∈ values, invocations a ≤ 2 * (f a).2 + 1) :
    arithmeticMapInvocations invocations values + values.length + 1 ≤
      2 * (arithmeticMapWithWork f values).2 + 2 := by
  induction values with
  | nil => exact Nat.le_refl 2
  | cons a rest ih =>
    have hh := h a List.mem_cons_self
    have ht := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    simp only [arithmeticMapInvocations, arithmeticMapWithWork, List.length_cons]
    omega

theorem coarseIndexedInvocations_le_work {B : ℕ} (k q L n : ℕ) (source target : List ℕ)
    (two : BinaryFraction) (d offset : ℕ) (draws : CoarseThresholdDraws B d)
    (allowance : BinaryFraction) (start : ℕ) :
    coarseIndexedInvocations k q L n source target two d offset draws allowance start ≤
      2 * (coarseIndexedWithWork k q L n source target two d offset draws allowance start).2 + 1 := by
  induction d generalizing offset allowance start with
  | zero =>
    have hd := coarseDescriptorInvocations_le_work B 0 n offset
    have hp := compareInvocations_le_work allowance (nat (bitWordValue (coarseDescriptorWithWork B 0 n offset).1))
    simp only [coarseIndexedInvocations, coarseIndexedWithWork]
    split_ifs
    · simp only [leWithWork]
      omega
    · have hmap := arithmeticMapInvocations_with_indices_le_work
        (fun shift : Fin (2 * k + 1) =>
          let mismatch := coarseReadShiftWithWork k n target (coarsePaddedReadWithWork n source offset).1 start shift
          let value := coarseGridNatWithWork allowance.denominator allowance.denominator_pos mismatch.1
          (value.1, value.2 + mismatch.2))
        (fun shift : Fin (2 * k + 1) =>
          let mismatch := coarseReadShiftWithWork k n target (coarsePaddedReadWithWork n source offset).1 start shift
          coarseReadShiftInvocations k n target (coarsePaddedReadWithWork n source offset).1 start shift +
            coarseGridNatInvocations allowance.denominator allowance.denominator_pos mismatch.1 + 1)
        (List.finRange (2 * k + 1)) (by
          intro shift _
          have hs := coarseReadShiftInvocations_le_work k n target
            (coarsePaddedReadWithWork n source offset).1 start shift
          have hg := coarseGridNatInvocations_le_work allowance.denominator allowance.denominator_pos
            (coarseReadShiftWithWork k n target (coarsePaddedReadWithWork n source offset).1 start shift).1
          dsimp only
          omega)
      have hpadded := coarsePaddedReadInvocations_le_work n source offset
      simp only [List.length_finRange] at hmap
      simp only [leWithWork, coarsePaddedReadWithWork] at hpadded ⊢
      simp only [coarsePaddedReadWithWork] at hmap
      omega
  | succ d ih =>
    obtain ⟨draw, below⟩ := draws
    let capacity := bitPowerWithWork B.bits d
    let childOffset := fun i : Fin B => coarseChildOffsetWithWork offset (bitWordValue capacity.1) i.val
    let childSize := fun i : Fin B => coarseDescriptorWithWork B d n (bitWordValue (childOffset i).1)
    let evaluate := fun (i : Fin B) a s =>
      let evaluated := coarseIndexedWithWork k q L n source target two d
        (bitWordValue (childOffset i).1) (below i) a s
      let next := binaryNaturalAddWithWork s (bitWordValue (childSize i).1)
      (evaluated.1, evaluated.2 + 3 * ((childOffset i).2 + (childSize i).2 + next.2 + 3))
    let allocation := fun (i : Fin B) a s =>
      coarseIndexedInvocations k q L n source target two d
        (bitWordValue (childOffset i).1) (below i) a s +
        3 * (coarseChildOffsetInvocations offset (bitWordValue capacity.1) i.val +
          coarseDescriptorInvocations B d n (bitWordValue (childOffset i).1) +
          bitAddInvocations s.bits (bitWordValue (childSize i).1).bits false) + 1
    have he : ∀ i a s, allocation i a s ≤ 2 * (evaluate i a s).2 + 1 := by
      intro i a s
      have hr := ih (bitWordValue (childOffset i).1) (below i) a s
      have ho := coarseChildOffsetInvocations_le_work offset (bitWordValue capacity.1) i.val
      have hs := coarseDescriptorInvocations_le_work B d n (bitWordValue (childOffset i).1)
      have ha := bitAddInvocations_le_work s.bits (bitWordValue (childSize i).1).bits false
      change bitAddInvocations s.bits (bitWordValue (childSize i).1).bits false ≤
        (binaryNaturalAddWithWork s (bitWordValue (childSize i).1)).2 at ha
      change coarseChildOffsetInvocations offset (bitWordValue capacity.1) i.val ≤ (childOffset i).2 at ho
      change coarseDescriptorInvocations B d n (bitWordValue (childOffset i).1) ≤ (childSize i).2 at hs
      dsimp only [allocation, evaluate]
      omega
    have hc := coarseIndexChildrenInvocations_le_work k q L two (fun i => bitWordValue (childSize i).1)
      evaluate allocation he draw allowance (List.finRange B) start
    have hd := coarseDescriptorInvocations_le_work B (d + 1) n offset
    have hp := compareInvocations_le_work allowance
      (nat (bitWordValue (coarseDescriptorWithWork B (d + 1) n offset).1))
    have hb := bitPowerInvocations_le_work B.bits d
    simp only [coarseIndexedInvocations, coarseIndexedWithWork]
    split_ifs
    · simp only [leWithWork]
      omega
    · change coarseDescriptorInvocations B (d + 1) n offset +
        compareInvocations allowance (nat (bitWordValue (coarseDescriptorWithWork B (d + 1) n offset).1)) + 2 +
        bitPowerInvocations B.bits d +
        coarseIndexChildrenInvocations q L two (fun i => bitWordValue (childSize i).1)
          evaluate allocation draw allowance (List.finRange B) start + B + 1 ≤
        2 * ((coarseDescriptorWithWork B (d + 1) n offset).2 + capacity.2 +
          (coarseIndexChildren k q L two (fun i => bitWordValue (childSize i).1)
            evaluate draw allowance (List.finRange B) start).2 +
          (leWithWork (nat (bitWordValue (coarseDescriptorWithWork B (d + 1) n offset).1)) allowance).2 +
          Nat.size (bitWordValue (coarseDescriptorWithWork B (d + 1) n offset).1) + B + 1) + 1
      change bitPowerInvocations B.bits d ≤ capacity.2 at hb
      simp only [leWithWork]
      omega

end BinaryFraction
end EditApproximation

end OAI
