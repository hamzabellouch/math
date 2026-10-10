import OAI.Algebra.AuslanderReiten.Complete.CompleteTailFunctor
import OAI.Algebra.AuslanderReiten.HomComplex.FullHomAugmentedExt
import OAI.Algebra.AuslanderReiten.Homology.NatComparisonFunctor

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.CompleteComparison
universe u
variable {k R S : Type u} [Field k] [CharP k 2] [Ring R] [Algebra k R]
  [Ring S] [Algebra k S]
variable (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S)

private theorem augmented_square {A B X : ModuleCat.{u} R}
    {A' B' X' : ModuleCat.{u} S} (a : A' ⟶ B') (b : A ⟶ B)
    (u : A' ⟶ F.obj A) (v : B' ⟶ F.obj B)
    (π : B ⟶ X) (π' : B' ⟶ X') (e : X' ≅ F.obj X)
    (hab : a ≫ v = u ≫ F.map b) (hπ : v ≫ F.map π = π' ≫ e.hom) :
    a ≫ π' = (u ≫ F.map (b ≫ π)) ≫ e.inv := by
  apply (cancel_mono e.hom).1
  simp only [Category.assoc, e.inv_hom_id, Category.comp_id]
  rw [← hπ, ← Category.assoc, hab, Category.assoc, ← F.map_comp]

variable [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} S)]
variable [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesProjectiveObjects]

variable (K : CochainComplex (ModuleCat.{u} R) ℤ)
variable (hK : TotallyAcyclicComplex (R := R) (chainOfCochain K))
variable (hFK : TotallyAcyclicComplex (R := S) (chainOfCochain (functorComplex F K)))
variable (e : ModuleCat.of S (Cokernel (chainOfCochain (functorComplex F K)) 0) ≅
  F.obj (ModuleCat.of R (Cokernel (chainOfCochain K) 0)))
variable (hπ : (tailFunctorHom F K).f 0 ≫ F.map (((completeExtResolution (R := R) hK)).π.f 0) = ((completeExtResolution (R := S) hFK)).π.f 0 ≫ e.hom)
include hπ

def completeTailResolutionHom :
    ProjectiveResolution.Hom (completeExtResolution (R := S) hFK) (ResolutionProducts.mapResolution F (completeExtResolution (R := R) hK)) e.hom where
  hom := tailFunctorHom F K
  hom_f_zero_comp_π_f_zero := by
    erw [ResolutionProducts.mapResolution_π_zero, ChainComplex.single₀_map_f_zero]
    exact hπ

omit [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} S)]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.PreservesProjectiveObjects] in
theorem tailFunctor_augmentation (r : ℕ) (x : Cochain K K (r : ℤ)) :
    ResolutionProducts.natComparisonAugmentation (R := S) (completeExtResolution (R := S) hFK) r (cochainTailMap (functorComplex F K) (functorComplex F K) r (x.map F)) =
      ((tailFunctorHom F K).f r ≫
        F.map (ResolutionProducts.natComparisonAugmentation (R := R) (completeExtResolution (R := R) hK) r (cochainTailMap K K r x))) ≫
          e.inv := by
  exact augmented_square F
    (cochainTailMap (functorComplex F K) (functorComplex F K) r (x.map F) 0)
    (cochainTailMap K K r x 0) ((tailFunctorHom F K).f r) ((tailFunctorHom F K).f 0)
    ((completeExtResolution hK).π.f 0) ((completeExtResolution hFK).π.f 0) e
    (tailFunctorHom_cochain F K r 0 x) hπ

theorem restrictedEndExt_functor (r : ℕ) (x : Cocycle K K (r : ℤ)) :
    restrictedEndExt (k := k) (functorComplex F K) hFK r
      (fullHomCocycleMap F K K (r : ℤ) x) =
    ((Ext.mk₀ e.hom).comp
      ((restrictedEndExt (k := k) K hK r x).mapExactFunctor F) (zero_add r)).comp
        (Ext.mk₀ e.inv) (add_zero r) := by
  exact ResolutionProducts.natComparisonEndExt_map (k := k) F
    (completeExtResolution hK) (completeExtResolution hFK) e
    (completeTailResolutionHom F K hK hFK e hπ) r
    (cochainTailMap K K r x.val) (cochainTailMap_comm (k := k) K K r x)
    (cochainTailMap (functorComplex F K) (functorComplex F K) r
      (fullHomCocycleMap F K K (r : ℤ) x).val)
    (cochainTailMap_comm (k := k) _ _ r (fullHomCocycleMap F K K (r : ℤ) x))
    (tailFunctor_augmentation F K hK hFK e hπ r x.val)

theorem fullPositiveExtEquiv_functor_mk (n : ℕ) (x : Cocycle K K ((n+1 : ℕ) : ℤ)) :
    fullPositiveExtEquiv (k := k) (R := S) (functorComplex F K) (functorComplex F K) hFK hFK.toExactProjectiveComplex n
      (CohomologyClass.mk (fullHomCocycleMap F K K ((n+1 : ℕ) : ℤ) x)) =
    ((Ext.mk₀ e.hom).comp
      ((fullPositiveExtEquiv (k := k) (R := R) K K hK hK.toExactProjectiveComplex n
        (CohomologyClass.mk x)).mapExactFunctor F) (zero_add _)).comp
          (Ext.mk₀ e.inv) (add_zero _) := by
  rw [fullPositiveExtEquiv_mk, fullPositiveExtEquiv_mk]
  exact restrictedEndExt_functor (k := k) F K hK hFK e hπ (n+1) x

end ArExplicit.CompleteComparison

end

end OAI
