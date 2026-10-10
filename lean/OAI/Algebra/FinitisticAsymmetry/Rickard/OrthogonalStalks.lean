import Mathlib
import OAI.Algebra.FinitisticAsymmetry.Model

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex CochainComplex.HomComplex
namespace LittleFinitistic.Rickard
universe u
variable {R : Type u} [Ring R]
local instance orthogonalStalksHasDerivedCategory : HasDerivedCategory (ModuleCat.{u} R) :=
  HasDerivedCategory.standard _

lemma class_eq_zero_of_hom_exact (D : ModuleCat.{u} R)
    (L : CochainComplex (ModuleCat.{u} R) ℤ)
    (hex : ∀ j, ∀ f : D ⟶ L.X j, f ≫ L.d j (j+1) = 0 →
      ∃ g : D ⟶ L.X (j-1), g ≫ L.d (j-1) j = f)
    (n : ℤ) (x : CohomologyClass ((singleFunctor _ 0).obj D) L n) : x=0 := by
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective x
  obtain ⟨f, hf, rfl⟩ := Cocycle.fromSingleMk_surjective x n (by simp) (n+1) rfl
  rw [CohomologyClass.mk_eq_zero_iff,
    Cocycle.fromSingleMk_mem_coboundaries_iff f (by simp) (n+1) rfl hf (n-1) (by omega)]
  exact hex n f hf

lemma orthogonal_single_of_hom_exact (D : ModuleCat.{u} R)
    (L : CochainComplex (ModuleCat.{u} R) ℤ) [L.IsKInjective]
    (hex : ∀ j, ∀ f : D ⟶ L.X j, f ≫ L.d j (j+1) = 0 →
      ∃ g : D ⟶ L.X (j-1), g ≫ L.d (j-1) j = f)
    (n : ℤ) (f : (DerivedCategory.singleFunctor _ 0).obj D ⟶ (DerivedCategory.Q.obj L)⟦n⟧) :
    f=0 := by
  let S := (singleFunctor (ModuleCat R) 0).obj D
  have hz (g : (HomotopyCategory.quotient _ _).obj S ⟶
      (HomotopyCategory.quotient _ _).obj (L⟦n⟧)) : g=0 := by
    obtain ⟨x, rfl⟩ := (CohomologyClass.toHom_bijective S L n).surjective g
    rw [class_eq_zero_of_hom_exact D L hex n x, map_zero]
  have hz' (g : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj S) ⟶
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj (L⟦n⟧))) : g=0 := by
    obtain ⟨g, rfl⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
      ((HomotopyCategory.quotient _ _).obj S) (L⟦n⟧)).surjective g
    rw [hz g, Functor.map_zero]
  let es := (DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) 0).app D
  let eqs := (DerivedCategory.quotientCompQhIso (ModuleCat R)).app S
  let eql := (DerivedCategory.quotientCompQhIso (ModuleCat R)).app (L⟦n⟧)
  let en := (DerivedCategory.Q.commShiftIso n).app L
  apply (cancel_epi es.inv).mp
  apply (cancel_epi eqs.hom).mp
  apply (cancel_mono en.inv).mp
  apply (cancel_mono eql.inv).mp
  simpa only [Category.assoc, comp_zero, zero_comp] using
    hz' (eqs.hom ≫ es.inv ≫ f ≫ en.inv ≫ eql.inv)

end LittleFinitistic.Rickard

end

end OAI
