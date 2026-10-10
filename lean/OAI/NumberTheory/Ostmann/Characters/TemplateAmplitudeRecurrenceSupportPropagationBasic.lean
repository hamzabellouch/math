import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceSupport

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

lemma sourceState_copied_value {k j : ℕ} (P : ℤ) (h : CopiedState k j)
    (y : OutsideState k j) (i : {i:(schedule k j).Slot // (schedule k j).IsCopied j i}) :
    sourceState k j P h y i.val=h i := by
  simp only [sourceState,childState_copied,pairedState,ite_true]

lemma sourceState_outside_value {k j : ℕ} (P : ℤ) (h : CopiedState k j)
    (y : OutsideState k j) (i : {i:(schedule k j).Slot // (schedule k j).IsOutside j i}) :
    sourceState k j P h y i.val=y i := by
  simp only [sourceState,childState_outside,pairedState]

lemma CurrentAtomSupport.copied_pos {k j : ℕ} {P s : ℤ} {h : CopiedState k j}
    {y : OutsideState k j} (hs : CurrentAtomSupport k j s (sourceState k j P h y))
    (i : {i:(schedule k j).Slot // (schedule k j).IsCopied j i}) : 0<h i := by
  simpa only [sourceState_copied_value] using hs.positive i.val

lemma CurrentAtomSupport.outside_pos {k j : ℕ} {P s : ℤ} {h : CopiedState k j}
    {y : OutsideState k j} (hs : CurrentAtomSupport k j s (sourceState k j P h y))
    (i : {i:(schedule k j).Slot // (schedule k j).IsOutside j i}) : 0<y i := by
  simpa only [sourceState_outside_value] using hs.positive i.val

lemma CurrentAtomSupport.copied_pairwise {k j : ℕ} {P s : ℤ} {h : CopiedState k j}
    {y : OutsideState k j} (hs : CurrentAtomSupport k j s (sourceState k j P h y)) :
    Pairwise (fun i t => IsCoprime (h i) (h t)) := by
  intro i t hit
  simpa only [sourceState_copied_value] using hs.pairwise
    (show i.val≠t.val from fun e => hit (Subtype.ext e))

lemma CurrentAtomSupport.outside_pairwise {k j : ℕ} {P s : ℤ} {h : CopiedState k j}
    {y : OutsideState k j} (hs : CurrentAtomSupport k j s (sourceState k j P h y)) :
    Pairwise (fun i t => IsCoprime (y i) (y t)) := by
  intro i t hit
  simpa only [sourceState_outside_value] using hs.pairwise
    (show i.val≠t.val from fun e => hit (Subtype.ext e))

lemma CurrentAtomSupport.copied_outside_coprime {k j : ℕ} {P s : ℤ}
    {h : CopiedState k j} {y : OutsideState k j}
    (hs : CurrentAtomSupport k j s (sourceState k j P h y))
    (i : {i:(schedule k j).Slot // (schedule k j).IsCopied j i})
    (t : {i:(schedule k j).Slot // (schedule k j).IsOutside j i}) :
    IsCoprime (h i) (y t) := by
  have hne : i.val≠t.val := fun e => t.property.2 (e ▸ i.property)
  simpa only [sourceState_copied_value,sourceState_outside_value] using hs.pairwise hne

lemma CurrentAtomSupport.copied_pivot_coprime {k j : ℕ} (hj:j<k) {P s : ℤ}
    {h : CopiedState k j} {y : OutsideState k j}
    (hs : CurrentAtomSupport k j s (sourceState k j P h y))
    (i : {i:(schedule k j).Slot // (schedule k j).IsCopied j i}) : IsCoprime (h i) P := by
  have hne : i.val≠(pivotSlot k j hj).val := by
    intro e
    exact pivot_not_copied _ _ _ (pivotSlot k j hj).property (e ▸ i.property)
  have hh := hs.pairwise hne
  change IsCoprime (sourceState k j P h y i.val) (sourceState k j P h y (pivotSlot k j hj).val) at hh
  rw [sourceState_copied_value] at hh
  simpa only [sourceState,childState_pivot k j true _ _ _ (pivotSlot k j hj).property] using hh

lemma coprime_cross_of_reversal {A B HL HR s P v w : ℤ}
    (hA : A∣HL) (hB : B∣HR) (hs : IsCoprime A s) (hP : IsCoprime A P)
    (he : v*HR-w*HL=s*P) : IsCoprime A B := by
  obtain ⟨t,ht⟩ := hA
  have hh : IsCoprime A (v*HR+(-w*t)*A) := by
    convert hs.mul_right hP using 1
    rw [←he,ht]
    ring
  exact hh.of_add_mul_right_right.of_mul_right_right.of_isCoprime_of_dvd_right hB

lemma isCoprime_of_prime_factors_large {s A : ℤ} (hs : s≠0)
    (hlarge : ∀q:ℕ,Nat.Prime q → q∣A.natAbs → s.natAbs<q) : IsCoprime s A := by
  rw [Int.isCoprime_iff_nat_coprime]
  apply Nat.coprime_of_dvd
  intro q hq hqs hqA
  exact (not_le_of_gt (hlarge q hq hqA))
    (Nat.le_of_dvd (Int.natAbs_pos.mpr hs) hqs)

end Ostmann.Characters.Template

end

end OAI
