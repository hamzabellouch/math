import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

theorem extend_shortExact (e : c.Embedding c')
    (S : ShortComplex (HomologicalComplex C c)) (h : S.ShortExact) :
    (S.map (e.extendFunctor C)).ShortExact := by
  have := h.mono_f
  have := h.epi_g
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro j
  by_cases hj : ∃ i, e.f i = j
  · obtain ⟨i, hi⟩ := hj
    let E : ((S.map (e.extendFunctor C)).map (HomologicalComplex.eval C c' j)) ≅
        S.map (HomologicalComplex.eval C c i) :=
      ShortComplex.isoMk (S.X₁.extendXIso e hi) (S.X₂.extendXIso e hi)
        (S.X₃.extendXIso e hi)
        (by
          change (S.X₁.extendXIso e hi).hom ≫ S.f.f i =
            (HomologicalComplex.extendMap S.f e).f j ≫ (S.X₂.extendXIso e hi).hom
          rw [HomologicalComplex.extendMap_f _ _ hi]
          simp)
        (by
          change (S.X₂.extendXIso e hi).hom ≫ S.g.f i =
            (HomologicalComplex.extendMap S.g e).f j ≫ (S.X₃.extendXIso e hi).hom
          rw [HomologicalComplex.extendMap_f _ _ hi]
          simp)
    exact ShortComplex.shortExact_of_iso E.symm (h.map (HomologicalComplex.eval C c i))
  · have hj' : ∀ i, e.f i ≠ j := by simpa using hj
    have h₁ := S.X₁.isZero_extend_X e j hj'
    have h₂ := S.X₂.isZero_extend_X e j hj'
    have h₃ := S.X₃.isZero_extend_X e j hj'
    exact { exact := ShortComplex.exact_of_isZero_X₂ _ h₂
            mono_f := h₁.mono _
            epi_g := h₃.epi _ }

end ArExplicit

end

end OAI
