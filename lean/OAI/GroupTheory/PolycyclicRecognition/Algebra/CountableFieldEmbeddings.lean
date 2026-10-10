import Mathlib.Algebra.AlgebraicCard
import Mathlib.Data.Finsupp.Encodable
import Mathlib.FieldTheory.FinTrdeg
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.Localization.Cardinality

namespace OAI

/-! # Extending embeddings into an uncountable algebraically closed field

Finite transcendence bases can be sent to independent elements in an
uncountable field over a countable coefficient field. Algebraicity then
extends this embedding to the finitely generated field itself.
-/

noncomputable section
namespace PolycyclicRecognition

def independentAdjoinEquiv
    {F K E I : Type*} [Field F] [Field K] [Field E] [Algebra F K] [Algebra F E]
    {t : I → K} {s : I → E} (ht : AlgebraicIndependent F t)
    (hs : AlgebraicIndependent F s) :
    IntermediateField.adjoin F (Set.range t) ≃ₐ[F]
      IntermediateField.adjoin F (Set.range s) :=
  ht.aevalEquivField.symm.trans hs.aevalEquivField

theorem independentAdjoinEquiv_generator
    {F K E I : Type*} [Field F] [Field K] [Field E] [Algebra F K] [Algebra F E]
    {t : I → K} {s : I → E} (ht : AlgebraicIndependent F t)
    (hs : AlgebraicIndependent F s) (i : I) :
    (independentAdjoinEquiv ht hs
      ⟨t i, IntermediateField.subset_adjoin F (Set.range t) ⟨i, rfl⟩⟩ : E) = s i := by
  let p : MvPolynomial I F := MvPolynomial.X i
  have hpt : ht.aevalEquivField (algebraMap _ _ p) =
      ⟨t i, IntermediateField.subset_adjoin F (Set.range t) ⟨i, rfl⟩⟩ := by
    apply Subtype.ext
    simp only [AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe,
      p, MvPolynomial.aeval_X]
  rw [← hpt]
  change (hs.aevalEquivField (ht.aevalEquivField.symm
    (ht.aevalEquivField (algebraMap _ _ p))) : E) = s i
  rw [AlgEquiv.symm_apply_apply]
  simp only [AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe,
    p, MvPolynomial.aeval_X]

theorem countable_adjoin_of_algebraicIndependent
    {F E I : Type*} [Field F] [Field E] [Algebra F E]
    [Countable F] [Countable I] (t : I → E) (ht : AlgebraicIndependent F t) :
    Countable (IntermediateField.adjoin F (Set.range t)) := by
  have : Countable (FractionRing (MvPolynomial I F)) :=
    Cardinal.mk_le_aleph0_iff.mp (by
      rw [Cardinal.mk_fractionRing]
      exact Cardinal.mk_le_aleph0)
  exact ht.aevalEquivField.symm.injective.countable

theorem exists_transcendental_of_countable
    (F E : Type*) [CommRing F] [IsDomain F] [Field E] [Algebra F E]
    [Module.IsTorsionFree F E]
    [Countable F] [Uncountable E] : ∃ x : E, Transcendental F x := by
  by_contra! h
  apply Set.not_countable_univ (α := E)
  have he : {x : E | IsAlgebraic F x} = Set.univ := by
    ext x
    exact iff_true_intro (not_not.mp (h x))
  exact he ▸ Algebraic.countable F E

theorem exists_finite_algebraicIndependent
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [Countable F] [Uncountable E] (n : ℕ) :
    ∃ t : Fin n → E, AlgebraicIndependent F t := by
  classical
  induction n with
  | zero => exact ⟨Fin.elim0, algebraicIndependent_empty_type⟩
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih
    let B := Algebra.adjoin F (Set.range t)
    have : Countable B := ht.aevalEquiv.symm.injective.countable
    obtain ⟨a, ha⟩ := exists_transcendental_of_countable B E
    have hh := (ht.option_iff_transcendental a).mpr ha
    exact ⟨(fun o : Option (Fin n) => o.elim a t) ∘ finSuccEquiv n,
      hh.comp (finSuccEquiv n) (finSuccEquiv n).injective⟩

theorem nonempty_algHom_of_countable_finite_trdeg
    (F K E : Type*) [Field F] [Field K] [Field E]
    [Algebra F K] [Algebra F E] [Countable F] [Uncountable E]
    [IsAlgClosed E] [FinTrdeg F K] : Nonempty (K →ₐ[F] E) := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_isTranscendenceBasis F K
  obtain ⟨t, ht⟩ := exists_finite_algebraicIndependent F E (Fintype.card s)
  let y : s → E := t ∘ Fintype.equivFin s
  have hy : AlgebraicIndependent F y := ht.comp _ (Fintype.equivFin s).injective
  let B := IntermediateField.adjoin F (Set.range ((↑) : s → K))
  let C := IntermediateField.adjoin F (Set.range y)
  let f : B →ₐ[F] E := C.val.comp
    ((hs.1.aevalEquivField.symm.trans hy.aevalEquivField).toAlgHom)
  have : Algebra.IsAlgebraic B K := hs.isAlgebraic_field
  obtain ⟨g, _⟩ := (IsAlgClosed.surjective_domRestrict_of_isAlgebraic
    (K := F) (L := B) (M := E) (E := K)) f
  exact ⟨g⟩

end PolycyclicRecognition

end

end OAI
