import Mathlib
import OAI.Algebra.FinitisticAsymmetry.Transport.ProjectiveDimension

namespace OAI

section
section
noncomputable section
open CategoryTheory
namespace LittleFinitistic
universe u
variable (A : Type u) [Ring A]
section FiniteTransport
universe v
variable {R S : Type v} [Ring R] [Ring S]

lemma compactElement_orderIso {α β : Type*} [CompleteLattice α] [CompleteLattice β]
    (e : α ≃o β) {a : α} (h : IsCompactElement a) : IsCompactElement (e a) := by
  rw [isCompactElement_iff_exists_le_iSup_of_le_iSup]
  intro ι f hf
  have hf' : a ≤ ⨆ i, e.symm (f i) := by
    rw [← e.symm.map_iSup]
    exact (e.le_symm_apply).mpr hf
  obtain ⟨s, hs⟩ := h.exists_finset_of_le_iSup (fun i => e.symm (f i)) hf'
  refine ⟨s, ?_⟩
  simpa only [e.map_iSup, e.apply_symm_apply, Finset.sup_eq_iSup] using e.monotone hs

lemma moduleFinite_equivalence_iff (e : ModuleCat.{v} R ≌ ModuleCat.{v} S)
    (M : ModuleCat.{v} R) : Module.Finite S (e.functor.obj M) ↔ Module.Finite R M := by
  let o : Submodule R M ≃o Submodule S (e.functor.obj M) :=
    (ModuleCat.subobjectModule M).symm.trans
      ((Subobject.lowerEquivalence (MonoOver.congr M e)).toOrderIso.trans
        (ModuleCat.subobjectModule (e.functor.obj M)))
  rw [Module.finite_def, Module.finite_def, Submodule.fg_iff_compact,
    Submodule.fg_iff_compact]
  constructor
  · intro h
    simpa using compactElement_orderIso o.symm h
  · intro h
    simpa using compactElement_orderIso o h

lemma littleFinitisticDimension_le_big (R : Type v) [Ring R] :
    littleFinitisticDimension R ≤ bigFinitisticDimension R := by
  refine iSup_le fun M => iSup_le fun _ => iSup_le fun h => ?_
  exact le_iSup_of_le M (le_iSup_of_le h le_rfl)

lemma littleFinitisticDimension_le_of_equivalence
    (e : ModuleCat.{v} R ≌ ModuleCat.{v} S) :
    littleFinitisticDimension R ≤ littleFinitisticDimension S := by
  refine iSup_le fun M => iSup_le fun hM => iSup_le fun hpd => ?_
  have hf : Module.Finite S (e.functor.obj M) :=
    (moduleFinite_equivalence_iff e M).mpr hM
  have hd : projectiveDimension (e.functor.obj M) < ⊤ := by
    rwa [projectiveDimension_equivalence e M]
  exact le_iSup_of_le (e.functor.obj M) (le_iSup_of_le hf
    (le_iSup_of_le hd (le_of_eq (projectiveDimension_equivalence e M).symm)))

lemma littleFinitisticDimension_equivalence
    (e : ModuleCat.{v} R ≌ ModuleCat.{v} S) :
    littleFinitisticDimension R = littleFinitisticDimension S :=
  le_antisymm (littleFinitisticDimension_le_of_equivalence e)
    (littleFinitisticDimension_le_of_equivalence e.symm)

lemma bigFinitisticDimension_le_of_equivalence
    (e : ModuleCat.{v} R ≌ ModuleCat.{v} S) :
    bigFinitisticDimension R ≤ bigFinitisticDimension S := by
  refine iSup_le fun M => iSup_le fun hpd => ?_
  have hd : projectiveDimension (e.functor.obj M) < ⊤ := by
    rwa [projectiveDimension_equivalence e M]
  exact le_iSup_of_le (e.functor.obj M)
    (le_iSup_of_le hd (le_of_eq (projectiveDimension_equivalence e M).symm))

lemma bigFinitisticDimension_equivalence
    (e : ModuleCat.{v} R ≌ ModuleCat.{v} S) :
    bigFinitisticDimension R = bigFinitisticDimension S :=
  le_antisymm (bigFinitisticDimension_le_of_equivalence e)
    (bigFinitisticDimension_le_of_equivalence e.symm)

end FiniteTransport

end LittleFinitistic
end
end
end

end OAI
