import OAI.Algebra.Finitistic.Bar.ChainSplitting
import Mathlib.Algebra.Homology.HomologicalComplexLimits

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped DirectSum
noncomputable section
namespace DerivedBar
universe u
variable (D : Type u) [Ring D]

/-- The native algebraic direct sum, with its actual coproduct maps. -/
def moduleSumCocone (F : Discrete ℕ ⥤ ModuleCat.{u} D) : Cocone F where
  pt := ModuleCat.of D (⨁ r : ℕ, F.obj ⟨r⟩)
  ι := Discrete.natTrans (fun r => ModuleCat.ofHom (DirectSum.lof D ℕ (fun s => F.obj ⟨s⟩) r.as))

def moduleSumIsColimit (F : Discrete ℕ ⥤ ModuleCat.{u} D) : IsColimit (moduleSumCocone D F) where
  desc s := ModuleCat.ofHom (DirectSum.toModule D ℕ s.pt (M := fun r => F.obj ⟨r⟩)
    (fun r => (s.ι.app ⟨r⟩).hom))
  fac s j := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    simp only [moduleSumCocone, Discrete.natTrans_app, ModuleCat.hom_comp,
      ModuleCat.hom_ofHom, LinearMap.comp_apply, DirectSum.toModule_lof]

  uniq s m hm := by
    apply ModuleCat.hom_ext
    apply DirectSum.linearMap_ext
    intro r
    apply LinearMap.ext
    intro v
    have h := congrArg (fun f => f.hom v) (hm ⟨r⟩)
    change m.hom (DirectSum.lof D ℕ (fun s => F.obj ⟨s⟩) r v) = (s.ι.app ⟨r⟩).hom v at h
    simp only [moduleSumCocone, LinearMap.comp_apply, ModuleCat.hom_ofHom,
      DirectSum.toModule_lof]
    exact h

/-- The canonical summand map into the already constructed chain direct sum. -/
def directSumComplexInclusion (S : ℕ → ChainComplex (ModuleCat.{u} D) ℕ) (r : ℕ) :
    S r ⟶ directSumComplex S where
  f n := ModuleCat.ofHom (DirectSum.lof D ℕ (fun s => (S s).X n) r)
  comm' i j hij := by
    change j+1=i at hij
    subst i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    simp only [directSumComplex, ChainComplex.of_d, ModuleCat.hom_comp,
      ModuleCat.hom_ofHom]
    change DirectSum.lmap (fun r => ((S r).d (j+1) j).hom)
      (DirectSum.lof D ℕ (fun s => (S s).X (j+1)) r v) =
        DirectSum.lof D ℕ (fun s => (S s).X j) r (((S r).d (j+1) j).hom v)
    exact DirectSum.lmap_lof _ _ _

def directSumComplexCocone (S : ℕ → ChainComplex (ModuleCat.{u} D) ℕ) :
    Cocone (Discrete.functor S) where
  pt := directSumComplex S
  ι := Discrete.natTrans (fun r => directSumComplexInclusion D S r.as)

/-- The native componentwise chain direct sum is the actual categorical coproduct. -/
def directSumComplexIsColimit (S : ℕ → ChainComplex (ModuleCat.{u} D) ℕ) :
    IsColimit (directSumComplexCocone D S) := by
  apply HomologicalComplex.isColimitOfEval
  intro n
  exact moduleSumIsColimit D (Discrete.functor S ⋙ HomologicalComplex.eval _ _ n)
end DerivedBar

end

end OAI
