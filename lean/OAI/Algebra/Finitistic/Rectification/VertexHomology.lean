import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import OAI.Algebra.Finitistic.Rectification.VertexFunctor
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

namespace OAI
noncomputable section
open CategoryTheory HomologicalComplex
namespace LittleFinitistic.VertexHomology
universe u
variable {A B : Type u} [Ring A] [Ring B]
variable (β : B →+* A) (e : A) (he : e*e=e) (hc : ∀ b, e*β b=β b*e)

include he

/-- Actual vertex projection preserves homology, because it preserves the
short exact sequences already proved in VertexFunctor. -/
theorem preservesHomology : (VertexFunctor.functor β e hc).PreservesHomology :=
  ((Functor.exact_tfae (VertexFunctor.functor β e hc)).out 1 3).1
    (VertexFunctor.map_shortExact β e he hc)

/-- Homology of the actual vertex complex is the actual vertex of module homology. -/
def iso (X : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    (((VertexFunctor.functor β e hc).mapHomologicalComplex (.up ℤ)).obj X).homology n ≅
      (VertexFunctor.functor β e hc).obj (X.homology n) := by
  letI := preservesHomology β e he hc
  exact (X.sc n).mapHomologyIso (VertexFunctor.functor β e hc)

/-- This comparison respects every natural transformation of the vertex functors,
so it retains the algebra arrow actions as well as the vertex vector spaces. -/
theorem natural (e' : A) (he' : e'*e'=e') (hc' : ∀ b, e'*β b=β b*e')
    (τ : VertexFunctor.functor β e hc ⟶ VertexFunctor.functor β e' hc')
    (X : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    homologyMap ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app X) n ≫
      (iso β e' he' hc' X n).hom =
    (iso β e he hc X n).hom ≫ τ.app (X.homology n) := by
  let := preservesHomology β e he hc
  let := preservesHomology β e' he' hc'
  have h := ShortComplex.homologyMap_mapNatTrans (X.sc n) τ
  change homologyMap ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app X) n =
    (iso β e he hc X n).hom ≫ τ.app (X.homology n) ≫
      (iso β e' he' hc' X n).inv at h
  rw [h]
  simp
end LittleFinitistic.VertexHomology

end

end OAI
