import OAI.Algebra.Finitistic.Ordinary.OrdinarySupportedExtension
import Mathlib.Algebra.Homology.Additive

namespace OAI
noncomputable section
open CategoryTheory Limits
namespace LittleFinitistic.FunctorExtension
universe u v u' v' w w'
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
variable {D : Type u'} [Category.{v'} D] [HasZeroMorphisms D] [HasZeroObject D]
variable (F : C ⥤ D) [F.PreservesZeroMorphisms]
variable {I : Type w} {J : Type w'} {c : ComplexShape I} {c' : ComplexShape J}
variable (K : HomologicalComplex C c) (e : c.Embedding c') [e.IsRelIff]

omit [HasZeroObject D] [e.IsRelIff] in
/-- Mapping an extended complex retains its proved zero terms outside the embedded degrees. -/
theorem mappedSupport : ((F.mapHomologicalComplex c').obj (K.extend e)).IsStrictlySupported e where
  isZero j hj := F.map_isZero (K.isZero_extend_X e j hj)

/-- On the actual supported degrees, mapping and extension have the same original terms. -/
def restrictionIso : ((F.mapHomologicalComplex c').obj (K.extend e)).restriction e ≅
    (F.mapHomologicalComplex c).obj K :=
  HomologicalComplex.Hom.isoOfComponents (fun i => F.mapIso (K.extendXIso e (i := i) rfl)) (by
    intro i j _
    change F.map (K.extendXIso e (i := i) rfl).hom ≫ F.map (K.d i j) =
      F.map ((K.extend e).d (e.f i) (e.f j)) ≫ F.map (K.extendXIso e (i := j) rfl).hom
    rw [← F.map_comp,← F.map_comp]
    congr 1
    rw [HomologicalComplex.extend_d_eq _ _ rfl rfl]
    simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id])

/-- An actual chain isomorphism commuting a zero-preserving functor with extension by zero. -/
def iso : (F.mapHomologicalComplex c').obj (K.extend e) ≅
    ((F.mapHomologicalComplex c).obj K).extend e := by
  letI := mappedSupport F K e
  exact (OrdinarySimulation.SupportedExtension.iso ((F.mapHomologicalComplex c').obj (K.extend e)) e).symm ≪≫
    (e.extendFunctor D).mapIso (restrictionIso F K e)
end LittleFinitistic.FunctorExtension

end

end OAI
