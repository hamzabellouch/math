import OAI.Analysis.CircleDomains.Selection.CountablePriorRecursion
import Mathlib.SetTheory.Cardinal.Aleph

namespace OAI

/-! The first uncountable well-order has countable strict initial segments.
This is the precise index set for retaining every earlier path law. -/

open Set Function Cardinal Ordinal
open scoped Cardinal Ordinal

noncomputable section
namespace CircleDomainRigidity

abbrev FirstUncountable := (ω₁ : Ordinal.{0}).ToType

theorem firstUncountable_not_countable : ¬Countable FirstUncountable := by
  rw [← Cardinal.mk_le_aleph0_iff, Cardinal.mk_toType]
  simp

instance (i : FirstUncountable) : Countable (Iio i) := by
  let f : Iio i → Iio i.toOrd.val := fun j =>
    ⟨j.val.toOrd.val, (Ordinal.ToType.mk.symm.lt_iff_lt).mpr j.property⟩
  have hf : Injective f := by
    intro j k h
    apply Subtype.ext
    apply Ordinal.ToType.mk.symm.injective
    apply Subtype.ext
    exact congrArg (fun z : Iio i.toOrd.val => z.val) h
  let := (Cardinal.countable_Iio_of_lt_omega_one i.toOrd.property).to_subtype
  exact Function.Injective.countable hf

theorem exists_injective_firstUncountable {X : Type} (S : Set X)
    (hS : ¬S.Countable) : ∃ f : FirstUncountable → X,
      Injective f ∧ range f ⊆ S := by
  have hc : ℵ₁ ≤ Cardinal.mk S := by
    rw [Cardinal.aleph_one_le_iff, Cardinal.aleph0_lt_mk_iff]
    exact not_countable_iff.mp (Set.countable_coe_iff.not.mpr hS)
  have hcard : Cardinal.mk FirstUncountable ≤ Cardinal.mk S := by
    simpa only [FirstUncountable, Cardinal.mk_toType, Ordinal.card_omega] using hc
  obtain ⟨f⟩ := (Cardinal.le_def _ _).mp hcard
  exact ⟨fun i => (f i).val, Subtype.val_injective.comp f.injective,
    by rintro x ⟨i, rfl⟩; exact (f i).property⟩

end CircleDomainRigidity

end

end OAI
