import OAI.Algebra.AuslanderReiten.Homology.FullPositiveNaturality
import OAI.Algebra.AuslanderReiten.Complete.CompleteTailCanonical
import OAI.Algebra.AuslanderReiten.Ext.ExtIsoFunctor

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits HomologicalComplex
open CochainComplex CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.CompleteComparison
universe u
variable {k R : Type u} [Field k] [CharP k 2] [Ring R] [Algebra k R]
variable [HasDerivedCategory (ModuleCat.{u} R)]
variable (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R) [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.PreservesProjectiveObjects]
variable (K : CochainComplex (ModuleCat.{u} R) ℤ)
variable (hK : TotallyAcyclicComplex (chainOfCochain K))
variable (hFK : TotallyAcyclicComplex (chainOfCochain (functorComplex F K)))

theorem fullPositiveExtEquiv_conjugatedFunctor
    (a : K ⟶ functorComplex F K) (b : functorComplex F K ⟶ K)
    (E : ModuleCat.of R (Cokernel (chainOfCochain K) 0) ≅
      F.obj (ModuleCat.of R (Cokernel (chainOfCochain K) 0)))
    (ha : ModuleCat.ofHom (cokernelMap (extendMap a negIndexEmbedding) 0) ≫
      (completeFunctorEndpointIso F K hK hFK).hom = E.hom)
    (hb : (completeFunctorEndpointIso F K hK hFK).inv ≫
      ModuleCat.ofHom (cokernelMap (extendMap b negIndexEmbedding) 0) = E.inv)
    (n : ℕ) (x : CohomologyClass K K ((n+1 : ℕ) : ℤ)) :
    fullPositiveExtEquiv (k := k) K K hK hK.toExactProjectiveComplex n
      (fullHomPostcomp b _ (fullHomPrecomp a _ (mapFullHom F K K _ x))) =
    selfExtIso (k := k) E.symm (n+1)
      ((fullPositiveExtEquiv (k := k) K K hK hK.toExactProjectiveComplex n x).mapExactFunctor F) := by
  rw [fullPositiveExtEquiv_postcomp hK hFK.toExactProjectiveComplex hK.toExactProjectiveComplex,
    fullPositiveExtEquiv_precomp hK hFK hFK.toExactProjectiveComplex]
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective x
  rw [mapFullHom_mk, fullPositiveExtEquiv_functor F K hK hFK]
  simp only [selfExtIso_apply, Iso.symm_inv, Iso.symm_hom]
  simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀_assoc,
    Ext.mk₀_comp_mk₀, ha, hb]

theorem fullHom_conjugatedFunctor_scalar
    (a : K ⟶ functorComplex F K) (b : functorComplex F K ⟶ K)
    (E : ModuleCat.of R (Cokernel (chainOfCochain K) 0) ≅
      F.obj (ModuleCat.of R (Cokernel (chainOfCochain K) 0)))
    (ha : ModuleCat.ofHom (cokernelMap (extendMap a negIndexEmbedding) 0) ≫
      (completeFunctorEndpointIso F K hK hFK).hom = E.hom)
    (hb : (completeFunctorEndpointIso F K hK hFK).inv ≫
      ModuleCat.ofHom (cokernelMap (extendMap b negIndexEmbedding) 0) = E.inv)
    (n : ℕ) (c : k)
    (hscalar : ∀ z : Ext (ModuleCat.of R (Cokernel (chainOfCochain K) 0))
        (ModuleCat.of R (Cokernel (chainOfCochain K) 0)) (n+1),
      selfExtIso (k := k) E.symm (n+1) (z.mapExactFunctor F) = c • z)
    (x : CohomologyClass K K ((n+1 : ℕ) : ℤ)) :
    fullHomPostcomp b _ (fullHomPrecomp a _ (mapFullHom F K K _ x)) = c • x := by
  apply (fullPositiveExtEquiv (k := k) K K hK hK.toExactProjectiveComplex n).injective
  rw [fullPositiveExtEquiv_conjugatedFunctor F K hK hFK a b E ha hb, hscalar, map_smul]

end ArExplicit.CompleteComparison

end

end OAI
