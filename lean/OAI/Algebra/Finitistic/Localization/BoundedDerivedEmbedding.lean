import OAI.Algebra.Finitistic.Localization.FiniteProjectiveHomotopy
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.CategoryTheory.EssentialImage

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.FiniteProjectiveHomotopy
universe u v
variable (R : Type u) [Ring R]

instance underlyingKProjective (T : K.{u,v} R) : CochainComplex.IsKProjective T.obj.as := by
  obtain ⟨⟨a,b,hb⟩,hp⟩ := T.property
  have : ∀ n, Projective (T.obj.as.X n) := fun n => (hp n).2
  have : CochainComplex.IsStrictlyLE T.obj.as b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact hb i (Or.inr hi)
  exact CochainComplex.isKProjective_of_projective T.obj.as b

/-- The canonical derived-category functor on the actual bounded projective source. -/
def derivedEmbedding : K.{u,v} R ⥤ DerivedCategory (ModuleCat.{v} R) :=
  inclusion R ⋙ DerivedCategory.Qh

instance derivedEmbeddingFaithful : (derivedEmbedding.{u,v} R).Faithful where
  map_injective {M N} {f g} h := by
    apply (inclusion R).map_injective
    exact (CochainComplex.IsKProjective.Qh_map_bijective M.obj.as N.obj).injective h

instance derivedEmbeddingFull : (derivedEmbedding.{u,v} R).Full where
  map_surjective {M N} f := by
    obtain ⟨g,hg⟩ := (CochainComplex.IsKProjective.Qh_map_bijective M.obj.as N.obj).surjective f
    refine ⟨(inclusion R).preimage g,?_⟩
    change DerivedCategory.Qh.map ((inclusion R).map ((inclusion R).preimage g)) = f
    erw [Functor.map_preimage]
    exact hg

instance derivedEmbeddingShift : (derivedEmbedding.{u,v} R).CommShift ℤ :=
  inferInstanceAs ((inclusion R ⋙ DerivedCategory.Qh).CommShift ℤ)
instance derivedEmbeddingTriangulated : (derivedEmbedding.{u,v} R).IsTriangulated :=
  inferInstanceAs (inclusion R ⋙ DerivedCategory.Qh).IsTriangulated

/-- Bounded complexes of f.g. projectives form a full subcategory of the actual derived category. -/
def boundedDerivedEquivalence : K.{u,v} R ≌ (derivedEmbedding.{u,v} R).EssImageSubcategory :=
  (derivedEmbedding R).toEssImage.asEquivalence
end LittleFinitistic.FiniteProjectiveHomotopy

end

end OAI
