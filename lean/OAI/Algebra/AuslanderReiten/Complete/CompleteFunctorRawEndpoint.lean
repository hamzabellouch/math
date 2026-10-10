import OAI.Algebra.AuslanderReiten.Complete.CompleteTailEndpoint
import OAI.Algebra.AuslanderReiten.Cones.CochainCokernel

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace ArExplicit.CompleteComparison
universe u
variable {R S : Type u} [Ring R] [Ring S]

def rawAugmentation (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    K.X 0 ⟶ ModuleCat.of R (CochainCokernel K) :=
  ModuleCat.ofHom (LinearMap.range (K.d (-1) 0).hom).mkQ

theorem rawAugmentation_coordinates (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : TotallyAcyclicComplex (chainOfCochain K)) :
    (completeExtResolution hK).π.f 0 ≫ (cochainCokernelLinearEquiv K).toModuleIso.hom =
      (tailTermIso K 0).hom ≫ rawAugmentation K := by
  erw [nonnegativeTailAugmentation_f_zero]
  rfl

private theorem raw_square {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {K₀ P₀ X X' : C} {FK₀ FP₀ Y Y' : D}
    (t : P₀ ≅ K₀) (s : FP₀ ≅ FK₀) (u : FK₀ ≅ F.obj K₀)
    (e : X ≅ X') (d : Y ≅ Y') (E : Y ≅ F.obj X)
    (p : P₀ ⟶ X) (q : K₀ ⟶ X') (p' : FP₀ ⟶ Y) (q' : FK₀ ⟶ Y')
    (h : p ≫ e.hom = t.hom ≫ q) (h' : p' ≫ d.hom = s.hom ≫ q')
    (hE : (s.hom ≫ u.hom ≫ F.map t.inv) ≫ F.map p = p' ≫ E.hom) :
    u.hom ≫ F.map q = q' ≫ d.inv ≫ E.hom ≫ F.map e.hom := by
  apply (cancel_epi s.hom).1
  calc
    s.hom ≫ u.hom ≫ F.map q =
        ((s.hom ≫ u.hom ≫ F.map t.inv) ≫ F.map p) ≫ F.map e.hom := by
      simp only [Category.assoc, ← F.map_comp, h, t.inv_hom_id_assoc]
    _ = (p' ≫ E.hom) ≫ F.map e.hom := congrArg (fun z => z ≫ F.map e.hom) hE
    _ = s.hom ≫ q' ≫ d.inv ≫ E.hom ≫ F.map e.hom := by
      have hp : p' = s.hom ≫ q' ≫ d.inv := by
        rw [← Category.assoc, ← h']
        simp
      rw [hp]
      simp only [Category.assoc]

variable (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.PreservesProjectiveObjects]
variable (K : CochainComplex (ModuleCat.{u} R) ℤ)
variable (hK : TotallyAcyclicComplex (chainOfCochain K))
variable (hFK : TotallyAcyclicComplex (chainOfCochain (functorComplex F K)))

def rawFunctorEndpointIso : ModuleCat.of S (CochainCokernel (functorComplex F K)) ≅
    F.obj (ModuleCat.of R (CochainCokernel K)) :=
  (cochainCokernelLinearEquiv (functorComplex F K)).symm.toModuleIso ≪≫
    completeFunctorEndpointIso F K hK hFK ≪≫ F.mapIso (cochainCokernelLinearEquiv K).toModuleIso

theorem rawFunctorEndpointIso_augmentation :
    F.map (rawAugmentation K) =
      rawAugmentation (functorComplex F K) ≫ (rawFunctorEndpointIso F K hK hFK).hom := by
  have ht := raw_square F (tailTermIso K 0) (tailTermIso (functorComplex F K) 0)
    (Iso.refl (F.obj (K.X 0))) (cochainCokernelLinearEquiv K).toModuleIso
    (cochainCokernelLinearEquiv (functorComplex F K)).toModuleIso
    (completeFunctorEndpointIso F K hK hFK)
    ((completeExtResolution hK).π.f 0) (rawAugmentation K)
    ((completeExtResolution hFK).π.f 0) (rawAugmentation (functorComplex F K))
    (rawAugmentation_coordinates K hK) (rawAugmentation_coordinates (functorComplex F K) hFK)
    (by
      change ((tailTermIso (functorComplex F K) 0).hom ≫
        F.map (tailTermIso K 0).inv) ≫ F.map ((completeExtResolution hK).π.f 0) = _
      exact completeFunctorEndpointIso_augmentation F K hK hFK)
  change (𝟙 _ ≫ F.map (rawAugmentation K)) =
    rawAugmentation (functorComplex F K) ≫ (rawFunctorEndpointIso F K hK hFK).hom at ht
  simpa only [Category.id_comp] using ht

end ArExplicit.CompleteComparison

end

end OAI
