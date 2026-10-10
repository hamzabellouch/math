import OAI.Combinatorics.EditApproximation.Coarse.CoarseAccessAllocation
import OAI.Combinatorics.EditApproximation.Coarse.CoarseChildAllocation
import OAI.Combinatorics.EditApproximation.Coarse.CoarseIndexedExecution

namespace OAI

namespace EditApproximation
namespace BinaryFraction

/-- Fresh bit and list cells in the actual indexed coarse evaluator.
Input arrays and random draws are shared; virtual source trees are never
materialized. Child offsets/descriptors follow the repeated reads charged
by the executable evaluator. -/
def coarseIndexedAllocation {B : ℕ} (k q L n : ℕ) (source target : List ℕ)
    (two : BinaryFraction) : (d offset : ℕ) → CoarseThresholdDraws B d →
    BinaryFraction → ℕ → ℕ
  | 0, offset, _, allowance, start =>
    let descriptor := coarseDescriptorWithWork B 0 n offset
    let size := bitWordValue descriptor.1
    let prune := leWithWork (nat size) allowance
    let setup := coarseDescriptorAllocation B 0 n offset + allowance.ltAllocation (nat size) +
      Nat.size size + 1
    if prune.1 then setup else
      let letter := coarsePaddedReadWithWork n source offset
      setup + Nat.size n + Nat.size offset +
        arithmeticMapAllocation (fun shift : Fin (2 * k + 1) =>
          let mismatch := coarseReadShiftWithWork k n target letter.1 start shift
          coarseReadShiftAllocation k n letter.1 start shift +
            coarseGridNatAllocation allowance.denominator allowance.denominator_pos mismatch.1)
          (List.finRange (2 * k + 1)) + 2 * (2 * k + 1)
  | d + 1, offset, (draws, below), allowance, start =>
    let descriptor := coarseDescriptorWithWork B (d + 1) n offset
    let size := bitWordValue descriptor.1
    let prune := leWithWork (nat size) allowance
    let setup := coarseDescriptorAllocation B (d + 1) n offset + allowance.ltAllocation (nat size) +
      Nat.size size + 1
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
        coarseIndexedAllocation k q L n source target two d
          (bitWordValue (childOffset i).1) (below i) a s +
          3 * (coarseChildOffsetAllocation offset (bitWordValue capacity.1) i.val +
            coarseDescriptorAllocation B d n (bitWordValue (childOffset i).1) +
            bitAddAllocation s.bits (bitWordValue (childSize i).1).bits false)
      setup + bitPowerAllocation B.bits d +
        coarseIndexChildrenAllocation q L two (fun i => bitWordValue (childSize i).1)
          evaluate allocation draws allowance (List.finRange B) start + B

theorem coarseIndexedAllocation_le_work {B : ℕ} (k q L n : ℕ) (source target : List ℕ)
    (two : BinaryFraction) (d offset : ℕ) (draws : CoarseThresholdDraws B d)
    (allowance : BinaryFraction) (start : ℕ) :
    coarseIndexedAllocation k q L n source target two d offset draws allowance start ≤
      2 * (coarseIndexedWithWork k q L n source target two d offset draws allowance start).2 := by
  induction d generalizing offset allowance start with
  | zero =>
    have hd := coarseDescriptorAllocation_le_work B 0 n offset
    have hp := ltAllocation_le_work allowance (nat (bitWordValue (coarseDescriptorWithWork B 0 n offset).1))
    simp only [coarseIndexedAllocation, coarseIndexedWithWork]
    split_ifs
    · simp only [leWithWork]
      omega
    · have hmap := arithmeticMapAllocation_le_work
        (fun shift : Fin (2 * k + 1) =>
          let mismatch := coarseReadShiftWithWork k n target (coarsePaddedReadWithWork n source offset).1 start shift
          let value := coarseGridNatWithWork allowance.denominator allowance.denominator_pos mismatch.1
          (value.1, value.2 + mismatch.2))
        (fun shift : Fin (2 * k + 1) =>
          let mismatch := coarseReadShiftWithWork k n target (coarsePaddedReadWithWork n source offset).1 start shift
          coarseReadShiftAllocation k n (coarsePaddedReadWithWork n source offset).1 start shift +
            coarseGridNatAllocation allowance.denominator allowance.denominator_pos mismatch.1)
        (List.finRange (2 * k + 1)) (by
          intro shift _
          have hs := coarseReadShiftAllocation_le_work k n target
            (coarsePaddedReadWithWork n source offset).1 start shift
          have hg := coarseGridNatAllocation_le_work allowance.denominator allowance.denominator_pos
            (coarseReadShiftWithWork k n target (coarsePaddedReadWithWork n source offset).1 start shift).1
          dsimp only
          omega)
      simp only [leWithWork, coarsePaddedReadWithWork]
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
      coarseIndexedAllocation k q L n source target two d
        (bitWordValue (childOffset i).1) (below i) a s +
        3 * (coarseChildOffsetAllocation offset (bitWordValue capacity.1) i.val +
          coarseDescriptorAllocation B d n (bitWordValue (childOffset i).1) +
          bitAddAllocation s.bits (bitWordValue (childSize i).1).bits false)
    have he : ∀ i a s, allocation i a s ≤ 2 * (evaluate i a s).2 := by
      intro i a s
      have hr := ih (bitWordValue (childOffset i).1) (below i) a s
      have ho := coarseChildOffsetAllocation_le_work offset (bitWordValue capacity.1) i.val
      have hs := coarseDescriptorAllocation_le_work B d n (bitWordValue (childOffset i).1)
      have ha := bitAddAllocation_le_work s.bits (bitWordValue (childSize i).1).bits false
      change bitAddAllocation s.bits (bitWordValue (childSize i).1).bits false ≤
        (binaryNaturalAddWithWork s (bitWordValue (childSize i).1)).2 at ha
      change coarseChildOffsetAllocation offset (bitWordValue capacity.1) i.val ≤ (childOffset i).2 at ho
      change coarseDescriptorAllocation B d n (bitWordValue (childOffset i).1) ≤ (childSize i).2 at hs
      dsimp only [allocation, evaluate]
      omega
    have hc := coarseIndexChildrenAllocation_le_work k q L two (fun i => bitWordValue (childSize i).1)
      evaluate allocation he draw allowance (List.finRange B) start
    have hd := coarseDescriptorAllocation_le_work B (d + 1) n offset
    have hp := ltAllocation_le_work allowance
      (nat (bitWordValue (coarseDescriptorWithWork B (d + 1) n offset).1))
    have hb := bitPowerAllocation_le_work B.bits d
    simp only [coarseIndexedAllocation, coarseIndexedWithWork]
    split_ifs
    · simp only [leWithWork]
      omega
    · change coarseDescriptorAllocation B (d + 1) n offset +
        allowance.ltAllocation (nat (bitWordValue (coarseDescriptorWithWork B (d + 1) n offset).1)) +
        Nat.size (bitWordValue (coarseDescriptorWithWork B (d + 1) n offset).1) + 1 +
        bitPowerAllocation B.bits d +
        coarseIndexChildrenAllocation q L two (fun i => bitWordValue (childSize i).1)
          evaluate allocation draw allowance (List.finRange B) start + B ≤
        2 * ((coarseDescriptorWithWork B (d + 1) n offset).2 + capacity.2 +
          (coarseIndexChildren k q L two (fun i => bitWordValue (childSize i).1)
            evaluate draw allowance (List.finRange B) start).2 +
          (leWithWork (nat (bitWordValue (coarseDescriptorWithWork B (d + 1) n offset).1)) allowance).2 +
          Nat.size (bitWordValue (coarseDescriptorWithWork B (d + 1) n offset).1) + B + 1)
      change bitPowerAllocation B.bits d ≤ capacity.2 at hb
      simp only [leWithWork]
      omega

end BinaryFraction
end EditApproximation

end OAI
