import Mathlib.CategoryTheory.Abelian.Projective.Ext
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace ArExplicit.ResolutionProducts
universe u v u' v'
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]
variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
variable [F.PreservesProjectiveObjects]
variable {X : C} (P : ProjectiveResolution X)

def mapResolution : ProjectiveResolution (F.obj X) where
  complex := (F.mapHomologicalComplex (.down ℕ)).obj P.complex
  projective n := F.projective_obj_of_projective (P.projective n)
  π := (F.mapHomologicalComplex (.down ℕ)).map P.π ≫
    (singleMapHomologicalComplex F (.down ℕ) 0).hom.app X
  quasiIso := by infer_instance

end ArExplicit.ResolutionProducts

end

end OAI
