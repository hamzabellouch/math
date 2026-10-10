import OAI.Algebra.AuslanderReiten.Complete.CompleteFunctorRawEndpoint
import OAI.Algebra.AuslanderReiten.Complete.CompleteCokernelLifts
import OAI.Algebra.AuslanderReiten.Homology.FullPositiveFunctorAction
import OAI.Algebra.AuslanderReiten.Ext.ExtFunctorScalar

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits HomologicalComplex
open CochainComplex.HomComplex
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

private theorem endpoint_before {C : Type*} [Category* C]
    {X X' Y Y' Z Z' : C} (d : X ≅ X') (e : Y ≅ Y') (c : Y ≅ Z)
    (f : Z ≅ Z') (E : X' ≅ Z') (a : X ⟶ Y)
    (ha : a ≫ e.hom = d.hom ≫ (E ≪≫ (e.symm ≪≫ c ≪≫ f).symm).hom) :
    a ≫ c.hom = (d ≪≫ E ≪≫ f.symm).hom := by
  have ht := congrArg (fun z => z ≫ e.inv ≫ c.hom) ha
  simpa only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id] using ht

private theorem endpoint_after {C : Type*} [Category* C]
    {X X' Y Y' Z Z' : C} (d : X ≅ X') (e : Y ≅ Y') (c : Y ≅ Z)
    (f : Z ≅ Z') (E : X' ≅ Z') (b : Y ⟶ X)
    (hb : b ≫ d.hom = e.hom ≫ (e.symm ≪≫ c ≪≫ f ≪≫ E.symm).hom) :
    c.inv ≫ b = (d ≪≫ E ≪≫ f.symm).inv := by
  apply (cancel_mono d.hom).1
  have ht := congrArg (fun z => c.inv ≫ z) hb
  simpa only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id] using ht

omit [HasDerivedCategory (ModuleCat.{u} R)] in
theorem cokernelMap_coordinates {L M : CochainComplex (ModuleCat.{u} R) ℤ} (f : L ⟶ M) :
    ModuleCat.ofHom (cokernelMap (extendMap f negIndexEmbedding) 0) ≫
      (cochainCokernelLinearEquiv M).toModuleIso.hom =
    (cochainCokernelLinearEquiv L).toModuleIso.hom ≫ ModuleCat.ofHom (cochainCokernelMap f) := by
  apply ModuleCat.hom_ext
  exact cochainCokernelLinearEquiv_natural f

omit [HasDerivedCategory (ModuleCat.{u} R)] in
theorem rawFunctor_precomp_endpoint
    (a : K ⟶ functorComplex F K)
    (E : ModuleCat.of R (CochainCokernel K) ≅ F.obj (ModuleCat.of R (CochainCokernel K)))
    (ha : cochainCokernelMap a =
      (E ≪≫ (rawFunctorEndpointIso F K hK hFK).symm).hom.hom) :
    ModuleCat.ofHom (cokernelMap (extendMap a negIndexEmbedding) 0) ≫
      (completeFunctorEndpointIso F K hK hFK).hom =
    ((cochainCokernelLinearEquiv K).toModuleIso ≪≫ E ≪≫
      F.mapIso (cochainCokernelLinearEquiv K).symm.toModuleIso).hom := by
  have hh := cokernelMap_coordinates a
  rw [ha] at hh
  exact endpoint_before (cochainCokernelLinearEquiv K).toModuleIso
    (cochainCokernelLinearEquiv (functorComplex F K)).toModuleIso
    (completeFunctorEndpointIso F K hK hFK)
    (F.mapIso (cochainCokernelLinearEquiv K).toModuleIso) E _ hh

omit [HasDerivedCategory (ModuleCat.{u} R)] in
theorem rawFunctor_postcomp_endpoint
    (b : functorComplex F K ⟶ K)
    (E : ModuleCat.of R (CochainCokernel K) ≅ F.obj (ModuleCat.of R (CochainCokernel K)))
    (hb : cochainCokernelMap b =
      (rawFunctorEndpointIso F K hK hFK ≪≫ E.symm).hom.hom) :
    (completeFunctorEndpointIso F K hK hFK).inv ≫
      ModuleCat.ofHom (cokernelMap (extendMap b negIndexEmbedding) 0) =
    ((cochainCokernelLinearEquiv K).toModuleIso ≪≫ E ≪≫
      F.mapIso (cochainCokernelLinearEquiv K).symm.toModuleIso).inv := by
  have hh := cokernelMap_coordinates b
  rw [hb] at hh
  exact endpoint_after (cochainCokernelLinearEquiv K).toModuleIso
    (cochainCokernelLinearEquiv (functorComplex F K)).toModuleIso
    (completeFunctorEndpointIso F K hK hFK)
    (F.mapIso (cochainCokernelLinearEquiv K).toModuleIso) E _ hh

theorem fullHom_rawFunctor_scalar
    (a : K ⟶ functorComplex F K) (b : functorComplex F K ⟶ K)
    (E : ModuleCat.of R (CochainCokernel K) ≅ F.obj (ModuleCat.of R (CochainCokernel K)))
    (ha : cochainCokernelMap a =
      (E ≪≫ (rawFunctorEndpointIso F K hK hFK).symm).hom.hom)
    (hb : cochainCokernelMap b =
      (rawFunctorEndpointIso F K hK hFK ≪≫ E.symm).hom.hom)
    (n : ℕ) (c : k)
    (hs : ∀ z : Ext (ModuleCat.of R (CochainCokernel K))
      (ModuleCat.of R (CochainCokernel K)) (n+1),
      selfExtIso (k := k) E.symm (n+1) (z.mapExactFunctor F) = c • z)
    (x : CohomologyClass K K ((n+1 : ℕ) : ℤ)) :
    fullHomPostcomp b _ (fullHomPrecomp a _ (mapFullHom F K K _ x)) = c • x := by
  apply fullHom_conjugatedFunctor_scalar F K hK hFK a b
    ((cochainCokernelLinearEquiv K).toModuleIso ≪≫ E ≪≫
      F.mapIso (cochainCokernelLinearEquiv K).symm.toModuleIso)
    (rawFunctor_precomp_endpoint F K hK hFK a E ha)
    (rawFunctor_postcomp_endpoint F K hK hFK b E hb) n c
  exact exactFunctor_scalar_transport F (cochainCokernelLinearEquiv K).toModuleIso E (n+1) c hs

end ArExplicit.CompleteComparison

end

end OAI
