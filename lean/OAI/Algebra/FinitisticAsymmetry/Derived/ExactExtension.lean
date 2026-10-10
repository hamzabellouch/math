import Mathlib
import OAI.Algebra.FinitisticAsymmetry.Model

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.DerivedSupport
universe u v t t'
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type t} {ι' : Type t'} {c : ComplexShape ι} {c' : ComplexShape ι'}
variable (e : c.Embedding c') (S : ShortComplex (HomologicalComplex C c))

def extendEvalIso {j : ι} {j' : ι'} (hj : e.f j = j') :
    (S.map (e.extendFunctor C)).map (HomologicalComplex.eval C c' j') ≅
    S.map (HomologicalComplex.eval C c j) :=
  ShortComplex.isoMk (S.X₁.extendXIso e hj) (S.X₂.extendXIso e hj) (S.X₃.extendXIso e hj)
    (by
      change (S.X₁.extendXIso e hj).hom ≫ S.f.f j =
        (extendMap S.f e).f j' ≫ (S.X₂.extendXIso e hj).hom
      rw [extendMap_f _ e hj]
      simp)
    (by
      change (S.X₂.extendXIso e hj).hom ≫ S.g.f j =
        (extendMap S.g e).f j' ≫ (S.X₃.extendXIso e hj).hom
      rw [extendMap_f _ e hj]
      simp)

lemma extend_shortExact (hS : S.ShortExact) : (S.map (e.extendFunctor C)).ShortExact := by
  have h (j' : ι') : ((S.map (e.extendFunctor C)).map
      (HomologicalComplex.eval C c' j')).ShortExact := by
    by_cases hj' : ∃ j, e.f j = j'
    · obtain ⟨j, hj⟩ := hj'
      let := hS.mono_f
      let := hS.epi_g
      exact ShortComplex.shortExact_of_iso (extendEvalIso e S hj).symm
        (hS.map (HomologicalComplex.eval C c j))
    · have h₁ := S.X₁.isZero_extend_X e j' (fun j h => hj' ⟨j,h⟩)
      have h₂ := S.X₂.isZero_extend_X e j' (fun j h => hj' ⟨j,h⟩)
      have h₃ := S.X₃.isZero_extend_X e j' (fun j h => hj' ⟨j,h⟩)
      exact { exact := ShortComplex.exact_of_isZero_X₂ _ h₂
              mono_f := h₁.mono _
              epi_g := h₃.epi _ }
  exact { exact := HomologicalComplex.exact_of_degreewise_exact _ (fun j => (h j).exact)
          mono_f := HomologicalComplex.mono_of_mono_f _ (fun j => (h j).mono_f)
          epi_g := HomologicalComplex.epi_of_epi_f _ (fun j => (h j).epi_g) }

end LittleFinitistic.DerivedSupport

end

end OAI
