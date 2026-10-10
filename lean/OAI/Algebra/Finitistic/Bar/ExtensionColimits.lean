import OAI.Algebra.Finitistic.Bar.StrictSupportExtension
import Mathlib.Algebra.Homology.HomologicalComplexLimits

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex
noncomputable section
namespace DerivedBar
universe u v w w' z z'
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  {ι : Type w} {ι' : Type w'} {c : ComplexShape ι} {c' : ComplexShape ι'}
  (e : c.Embedding c')

/-- Evaluation of extension at an index in its image is the original evaluation,
naturally on all complexes and chain maps. -/
def extensionEvalIso (i : ι) (j : ι') (h : e.f i=j) :
    e.extendFunctor C ⋙ HomologicalComplex.eval C c' j ≅ HomologicalComplex.eval C c i :=
  NatIso.ofComponents (fun K => K.extendXIso e h) (by
    intro K L f
    change (HomologicalComplex.extendMap f e).f j ≫ (L.extendXIso e h).hom =
      (K.extendXIso e h).hom ≫ f.f i
    rw [HomologicalComplex.extendMap_f f e h]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

/-- Extension by zero preserves the actual colimit, proved degreewise including
the zero degrees. In particular it preserves the count coproduct. -/
theorem extensionPreservesColimit {J : Type z} [Category.{z'} J] [HasColimitsOfShape J C]
    (F : J ⥤ HomologicalComplex C c) : PreservesColimit F (e.extendFunctor C) := by
  classical
  apply preservesColimit_of_preserves_colimit_cocone (colimit.isColimit F)
  apply HomologicalComplex.isColimitOfEval
  intro j
  by_cases hj : ∃ i, e.f i=j
  · let i := hj.choose
    have hi : e.f i=j := hj.choose_spec
    letI : PreservesColimit F (e.extendFunctor C ⋙ HomologicalComplex.eval C c' j) :=
      preservesColimit_of_natIso F (extensionEvalIso e i j hi).symm
    exact isColimitOfPreserves (e.extendFunctor C ⋙ HomologicalComplex.eval C c' j) (colimit.isColimit F)
  · refine { desc := fun t => 0, fac := ?_, uniq := ?_ }
    · intro t obj
      exact ((F.obj obj).isZero_extend_X e j (not_exists.mp hj)).eq_of_src _ _
    · intro t m hm
      exact ((colimit F).isZero_extend_X e j (not_exists.mp hj)).eq_of_src _ _
end DerivedBar

end

end OAI
