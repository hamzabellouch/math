import OAI.Combinatorics.EditApproximation.Coarse.CoarseIndexedExtra

namespace OAI

namespace EditApproximation
namespace BinaryFraction

attribute [local irreducible] coarseIndexedWithWork coarseReadCore coarseIndexedExtra

theorem coarseIndexedWithWork_cost_compare {B : ℕ} (k q L n : ℕ) (source target : List ℕ)
    (two : BinaryFraction) (d offset : ℕ) (draws : CoarseThresholdDraws B d)
    (allowance : BinaryFraction) (start : ℕ) :
    (coarseIndexedWithWork k q L n source target two d offset draws allowance start).2 ≤
      (coarseReadCore k q L n source target two d offset draws allowance start).2 +
        coarseIndexedExtra k q L n source target two d offset draws allowance start := by
  induction d generalizing offset allowance start with
  | zero =>
    let f := fun shift : Fin (2 * k + 1) =>
      coarseGridNatWithWork allowance.denominator allowance.denominator_pos
        (coarseReadShiftCost k n target (coarsePaddedRead n source offset) start shift)
    let extra := fun shift : Fin (2 * k + 1) =>
      (coarseReadShiftWithWork k n target (coarsePaddedRead n source offset) start shift).2
    have hc := arithmeticMapWithWork_add_cost f extra (List.finRange (2 * k + 1))
    rw [coarseIndexedWithWork, coarseReadCore, coarseIndexedExtra]
    simp only [coarseDescriptorWithWork_value, coarsePaddedReadWithWork_value]
    split_ifs
    · omega
    · simp only [f, extra] at hc
      simp only [coarseReadShiftWithWork_value]
      omega
  | succ d ih =>
    obtain ⟨draws, below⟩ := draws
    let capacity := bitPowerWithWork B.bits d
    let childOffset := fun i : Fin B => coarseChildOffsetWithWork offset (bitWordValue capacity.1) i.val
    let childSize := fun i : Fin B => coarseDescriptorWithWork B d n (bitWordValue (childOffset i).1)
    let overhead := fun i : Fin B => fun s : ℕ =>
      3 * ((childOffset i).2 + (childSize i).2 +
        (binaryNaturalAddWithWork s (bitWordValue (childSize i).1)).2 + 3)
    let actual := fun i : Fin B => fun a s =>
      let evaluated := coarseIndexedWithWork k q L n source target two d
        (bitWordValue (childOffset i).1) (below i) a s
      (evaluated.1, evaluated.2 + overhead i s)
    let reference := fun i : Fin B =>
      coarseReadCore k q L n source target two d (offset + i.val * B ^ d) (below i)
    let extra := fun i : Fin B => fun a s =>
      coarseIndexedExtra k q L n source target two d (offset + i.val * B ^ d) (below i) a s + overhead i s
    have hv : ∀ i a s, (actual i a s).1 = (reference i a s).1 := by
      intro i a s
      simp only [actual, reference, childOffset, capacity, coarseChildOffsetWithWork_value,
        bitPowerWithWork_value, bitWordValue_bits]
      exact coarseIndexedWithWork_value k q L n source target two d _ _ a s
    have hw : ∀ i a s, (actual i a s).2 ≤ (reference i a s).2 + extra i a s := by
      intro i a s
      simp only [actual, reference, extra, childOffset, capacity, coarseChildOffsetWithWork_value,
        bitPowerWithWork_value, bitWordValue_bits]
      have h := ih (offset + i.val * B ^ d) (below i) a s
      omega
    have hloop := coarseIndexChildren_cost_compare k q L two
      (fun i => coarseDescriptorLength B d n (offset + i.val * B ^ d)) draws actual reference extra
      hv hw allowance (List.finRange B) start
    erw [coarseIndexedWithWork, coarseReadCore, coarseIndexedExtra]
    simp only [coarseDescriptorWithWork_value]
    split_ifs
    · omega
    · simp only [actual, reference, extra, overhead, childOffset, childSize, capacity,
        coarseDescriptorWithWork_value, coarseChildOffsetWithWork_value,
        bitPowerWithWork_value, bitWordValue_bits] at hloop ⊢
      omega

end BinaryFraction
end EditApproximation

end OAI
