import OAI.NumberTheory.TwoPoint.Bounds.ActualPrimeSlots
import OAI.NumberTheory.TwoPoint.Bounds.PrimeSlotClasses

namespace OAI

/-! Actual squarefree prime occurrences satisfy the code's class conditions. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

namespace PrimeSlotData

variable {R N : ℕ}

lemma code_value_injective (a : PrimeSlotData R N) :
    Function.Injective (fun z : a.code.usedClasses => a.prime z.val) := by
  intro z t h
  obtain ⟨i, _, hi⟩ := mem_image.mp z.property
  obtain ⟨j, _, hj⟩ := mem_image.mp t.property
  apply Subtype.ext
  rw [← hi, ← hj]
  apply (a.code_class_eq_iff i j).mpr
  have he : a.prime (a.code.2.1 i) = a.prime (a.code.2.1 j) := by
    simpa only [hi, hj] using h
  exact (a.code_class_prime i).symm.trans (he.trans
    (a.code_class_prime j))

lemma code_value_image (a : PrimeSlotData R N) :
    (univ.image (fun z : a.code.usedClasses => a.prime z.val)) = univ.image a.prime := by
  ext p
  constructor
  · rintro hp
    obtain ⟨z, _, rfl⟩ := mem_image.mp hp
    exact mem_image.mpr ⟨z.val, mem_univ _, rfl⟩
  · rintro hp
    obtain ⟨i, _, rfl⟩ := mem_image.mp hp
    exact mem_image.mpr ⟨a.code.classAt i, mem_univ _, a.code_class_prime i⟩

lemma code_kindConsistent (a : PrimeSlotData R N)
    (hk : ∀ i j, a.prime i = a.prime j → a.isPadding i = a.isPadding j) :
    a.code.KindConsistent := by
  intro j
  exact hk _ _ (a.code_class_prime j)

lemma code_rowInjective (a : PrimeSlotData R N)
    (hi : ∀ i j, a.row i = a.row j → a.isPadding i = a.isPadding j →
      a.prime i = a.prime j → i = j) : a.code.RowInjective := by
  intro r b i hi' j hj' he
  have hir := (mem_filter.mp hi').2
  have hjr := (mem_filter.mp hj').2
  exact hi i j (hir.1.trans hjr.1.symm) (hir.2.trans hjr.2.symm)
    ((a.code_class_eq_iff i j).mp he)

end PrimeSlotData

variable {R : ℕ}

lemma actualSlot_eq_of_data (w : Fin R → SignedStep) (s t : ActualPrimeSlot w)
    (hr : s.1 = t.1) (hk : actualSlotKind w s = actualSlotKind w t)
    (hp : actualSlotPrime w s = actualSlotPrime w t) : s = t := by
  rcases s with ⟨i, p | p⟩ <;> rcases t with ⟨j, q | q⟩ <;> cases hr
  · congr 2
    exact Subtype.ext hp
  · cases hk
  · cases hk
  · congr 2
    exact Subtype.ext hp

lemma actualSlot_kind_of_prime (w : Fin R → SignedStep)
    (hd : ∀ i j, Disjoint (w i).tuple.primeFactors (w j).padding.primeFactors)
    (s t : ActualPrimeSlot w) (hp : actualSlotPrime w s = actualSlotPrime w t) :
    actualSlotKind w s = actualSlotKind w t := by
  rcases s with ⟨i, p | p⟩ <;> rcases t with ⟨j, q | q⟩
  · rfl
  · change p.val = q.val at hp
    exact False.elim ((disjoint_left.mp (hd i j)) p.property
      (by simpa only [hp] using q.property))
  · change p.val = q.val at hp
    exact False.elim ((disjoint_left.mp (hd j i)) q.property
      (by simpa only [← hp] using p.property))
  · rfl

theorem actualPrimeSlotData_code_kindConsistent (w : Fin R → SignedStep)
    (hd : ∀ i j, Disjoint (w i).tuple.primeFactors (w j).padding.primeFactors) :
    (actualPrimeSlotData w).code.KindConsistent := by
  apply PrimeSlotData.code_kindConsistent
  intro i j hp
  exact actualSlot_kind_of_prime w hd _ _ hp

theorem actualPrimeSlotData_code_rowInjective (w : Fin R → SignedStep) :
    (actualPrimeSlotData w).code.RowInjective := by
  apply PrimeSlotData.code_rowInjective
  intro i j hr hk hp
  apply (actualPrimeSlotEquiv w).symm.injective
  exact actualSlot_eq_of_data w _ _ hr hk hp

end TwoPointCorrelations

end OAI
