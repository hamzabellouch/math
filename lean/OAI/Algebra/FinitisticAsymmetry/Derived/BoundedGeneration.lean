import Mathlib
import OAI.Algebra.FinitisticAsymmetry.Derived.Telescopes
import OAI.Algebra.FinitisticAsymmetry.Derived.Truncations

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits
open HomologicalComplex

open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.DerivedSupport

section
universe v w
variable {C : Type v} [Category.{w} C]

def eventuallyIsoCoconeIsColimit {F : ℕ ⥤ C} (c : Cocone F) (N : ℕ)
    (h : ∀ n, N ≤ n → IsIso (c.ι.app n)) : IsColimit c := by
  have := h N le_rfl
  refine { desc := fun s => inv (c.ι.app N) ≫ s.ι.app N, fac := ?_, uniq := ?_ }
  · intro s n
    let m := max n N
    have hm : N ≤ m := le_max_right _ _
    have := h m hm
    have he : inv (c.ι.app N) ≫ s.ι.app N = inv (c.ι.app m) ≫ s.ι.app m := by
      apply (cancel_epi (c.ι.app N)).1
      rw [IsIso.hom_inv_id_assoc, ← c.w (homOfLE hm)]
      simp only [Category.assoc, IsIso.hom_inv_id_assoc, s.w]
    rw [he, ← c.w (homOfLE (le_max_left n N))]
    simp only [m, Category.assoc, IsIso.hom_inv_id_assoc, s.w]
  · intro s m hm
    apply (cancel_epi (c.ι.app N)).1
    rw [IsIso.hom_inv_id_assoc, hm]

end

section
universe u
variable {R : Type u} [Ring R]
variable (K : CochainComplex (ModuleCat.{u} R) ℤ)

def cutSequenceMap (n : ℕ) : cut K (-(n : ℤ)) ⟶ cut K (-(n+1 : ℤ)) :=
  cutMap K (by omega)

def cutSequenceCocone : Cocone (Functor.ofSequence (cutSequenceMap K)) where
  pt := K
  ι := NatTrans.ofSequence (fun n => cutι K (-(n : ℤ))) (fun n => by
    simp [cutSequenceMap]
    exact (cutMap_ι K _).trans (Category.comp_id _).symm)

def cutSequenceIsColimit : IsColimit (cutSequenceCocone K) := by
  apply HomologicalComplex.isColimitOfEval
  intro j
  apply eventuallyIsoCoconeIsColimit _ (-j).toNat
  intro n hn
  change IsIso ((cutι K (-(n : ℤ))).f j)
  exact cutι_f_isIso K _ _ (by omega)

end

section
universe u w
variable {R : Type u} [Ring R]
variable (K : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
  (hK : ∀ j, b < j → IsZero (K.X j))

include hK in
lemma cut_isZero_of_upperBound (a : ℤ) (ha : b < a) : IsZero (cut K a) := by
  rw [IsZero.iff_id_eq_zero]
  apply HomologicalComplex.Hom.ext
  funext j
  have hz : IsZero ((cut K a).X j) := by
    by_cases h : a ≤ j
    · have := cutι_f_isIso K a j h
      exact (hK j (lt_of_lt_of_le ha h)).of_iso (asIso ((cutι K a).f j))
    · exact cut_isZero_X K a j (by omega)
  exact hz.eq_of_src _ _

variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]

include b hK in
lemma prop_cut_of_terms (P : ObjectProperty (DerivedCategory (ModuleCat.{u} R)))
    [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    (hterms : ∀ j, P (DerivedCategory.Q.obj
      ((HomologicalComplex.single (ModuleCat R) (ComplexShape.up ℤ) j).obj (K.X j))))
    (a : ℤ) : P (DerivedCategory.Q.obj (cut K a)) := by
  have step (a : ℤ) (ha : P (DerivedCategory.Q.obj (cut K (a+1)))) :
      P (DerivedCategory.Q.obj (cut K a)) :=
    P.ext_of_isTriangulatedClosed₂ _
      (DerivedCategory.triangleOfSES_distinguished (cut_shortExact K a)) ha (hterms a)
  have h (n : ℕ) : P (DerivedCategory.Q.obj (cut K (b+1-(n : ℤ)))) := by
    induction n with
    | zero =>
      exact P.prop_of_isZero (DerivedCategory.Q.map_isZero
        (cut_isZero_of_upperBound K b hK _ (by omega)))
    | succ n ih =>
      apply step
      convert ih using 1
      congr 2
      omega
  by_cases ha : a ≤ b+1
  · have he : b+1-((b+1-a).toNat : ℤ) = a := by omega
    simpa only [he] using h ((b+1-a).toNat)
  · exact P.prop_of_isZero (DerivedCategory.Q.map_isZero
      (cut_isZero_of_upperBound K b hK a (by omega)))

end

universe u w
variable {R : Type u} [Ring R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]
variable (P : ObjectProperty (DerivedCategory (ModuleCat.{u} R)))
  [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
  [P.IsClosedUnderColimitsOfShape (Discrete ℕ)]

omit [P.IsClosedUnderColimitsOfShape (Discrete ℕ)] in
lemma prop_single_of_zero (M : ModuleCat R)
    (hM : P ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj M)) (j : ℤ) :
    P (DerivedCategory.Q.obj
      ((HomologicalComplex.single (ModuleCat R) (ComplexShape.up ℤ) j).obj M)) := by
  apply P.prop_of_iso ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) j).app M)
  apply P.prop_of_iso (((DerivedCategory.singleFunctors (ModuleCat R)).shiftIso (-j) j 0 (by omega)).app M)
  exact P.le_shift (-j) _ hM

lemma prop_of_boundedAbove_terms (K : CochainComplex (ModuleCat R) ℤ)
    (b : ℤ) (hb : ∀ j, b < j → IsZero (K.X j))
    (hterms : ∀ j, P ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (K.X j))) :
    P (DerivedCategory.Q.obj K) := by
  exact localizing_sequence_colimit (fun n => cut K (-(n : ℤ))) (cutSequenceMap K)
    (cutSequenceCocone K) (cutSequenceIsColimit K) P
    (fun n => prop_cut_of_terms K b hb P (fun j => prop_single_of_zero P _ (hterms j) j) _)

end LittleFinitistic.DerivedSupport

end

end OAI
