import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteFinsuppHom
import OAI.GroupTheory.PolycyclicRecognition.Analysis.IntegralFinsuppFunctor
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic

namespace OAI

/-! # Direct sums in cohomology computed from finite group-ring resolutions -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2
attribute [local instance 2000] Rep.instLinear
attribute [local instance 2100] Linear.homModule

variable (k : Type) [CommRing k] (G : Type) [Group G] (α : Type)

theorem finiteFinsuppHomEquiv_precomp {A B C : Rep k G}
    [Module.Finite k[G] A.ρ.asModule] [Module.Finite k[G] B.ρ.asModule]
    (u : A ⟶ B) (x : α →₀ (B ⟶ C)) :
    finiteFinsuppHomEquiv k G α A C
        (Finsupp.mapRange.linearMap (Linear.leftComp k C u) x) =
      u ≫ finiteFinsuppHomEquiv k G α B C x := by
  apply Rep.hom_ext
  apply DFunLike.ext
  intro a
  apply Finsupp.ext
  intro i
  change ((finiteFinsuppHomEquiv k G α A C _).hom a) i =
    ((finiteFinsuppHomEquiv k G α B C x).hom (u.hom a)) i
  rw [finiteFinsuppHomEquiv_apply, finiteFinsuppHomEquiv_apply]
  rfl

def finsuppCochainsIso (P : ProjectiveResolution (Rep.trivial k G k))
    (hP : ∀ i, Module.Finite k[G] (P.complex.X i).ρ.asModule) (A : Rep k G) :
    ((moduleFinsuppFunctor k α).mapHomologicalComplex _).obj
        (P.complex.linearYonedaObj k A) ≅
      P.complex.linearYonedaObj k (Rep.finsupp α A) := by
  letI (i : ℕ) : Module.Finite k[G] (P.complex.X i).ρ.asModule := hP i
  refine HomologicalComplex.Hom.isoOfComponents
    (fun i => (finiteFinsuppHomEquiv k G α (P.complex.X i) A).toModuleIso) ?_
  intro i j _
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change P.complex.d j i ≫ finiteFinsuppHomEquiv k G α (P.complex.X i) A x =
    finiteFinsuppHomEquiv k G α (P.complex.X j) A
      (Finsupp.mapRange.linearMap (Linear.leftComp k A (P.complex.d j i)) x)
  exact (finiteFinsuppHomEquiv_precomp k G α (P.complex.d j i) x).symm

def finsuppCohomologyIso (P : ProjectiveResolution (Rep.trivial k G k))
    (hP : ∀ i, Module.Finite k[G] (P.complex.X i).ρ.asModule) (A : Rep k G) (i : ℕ) :
    groupCohomology (Rep.finsupp α A) i ≅
      (moduleFinsuppFunctor k α).obj (groupCohomology A i) :=
  groupCohomologyIso (Rep.finsupp α A) i P ≪≫
    (HomologicalComplex.homologyFunctor _ _ i).mapIso (finsuppCochainsIso k G α P hP A).symm ≪≫
      ((P.complex.linearYonedaObj k A).sc i).mapHomologyIso (moduleFinsuppFunctor k α) ≪≫
        (moduleFinsuppFunctor k α).mapIso (groupCohomologyIso A i P).symm

end PolycyclicRecognition

end

end OAI
