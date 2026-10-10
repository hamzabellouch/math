import OAI.Algebra.AuslanderReiten.Cones.MappingConeTotal
import OAI.Algebra.AuslanderReiten.Cones.CochainCokernel
import OAI.Algebra.AuslanderReiten.Cones.ConeQuotientMap

namespace OAI

noncomputable section
open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex

namespace ArExplicit

open CompleteComparison

universe u

variable {R : Type u} [Ring R]
variable {F G : CochainComplex (ModuleCat.{u} R) ℤ} (φ : F ⟶ G)

def conePreviousTermEquiv :
    (mappingCone φ).X (-1) ≃ₗ[R] (G.X (-1) × F.X 0) := by
  simpa using coneTermEquiv φ (-1)

def rawConeBlockEquiv : CochainCokernel (mappingCone φ) ≃ₗ[R]
    ConeQuotientMap.Cone (F.d 0 1).hom (G.d (-1) 0).hom (φ.f 0).hom :=
  cokernelLinearCongr _ _ (conePreviousTermEquiv φ) (coneTermEquiv φ 0) (by
    simpa [conePreviousTermEquiv] using coneTermEquiv_differential φ (-1))

def completeConeBlockEquiv : Cokernel (chainOfCochain (mappingCone φ)) 0 ≃ₗ[R]
    ConeQuotientMap.Cone (F.d 0 1).hom (G.d (-1) 0).hom (φ.f 0).hom :=
  (cochainCokernelLinearEquiv (mappingCone φ)).trans (rawConeBlockEquiv φ)

variable {L : Type u} [AddCommGroup L] [Module R L]
variable (p : CochainCokernel G →ₗ[R] L)
variable (hex : Function.Exact (cochainCokernelMap φ) p)

private theorem rawCokernelMap_comm :
    (LinearMap.range (G.d (-1) 0).hom).mkQ.comp (φ.f 0).hom =
    (cochainCokernelMap φ).comp (LinearMap.range (F.d (-1) 0).hom).mkQ := by
  apply LinearMap.ext
  intro x
  rfl

def rawConeQuotient : CochainCokernel (mappingCone φ) →ₗ[R] L :=
  (ConeQuotientMap.quotientMap (F.d (-1) 0).hom (F.d 0 1).hom
    (G.d (-1) 0).hom (φ.f 0).hom (cochainCokernelMap φ) p
    (rawCokernelMap_comm φ) hex).comp (rawConeBlockEquiv φ).toLinearMap

def completeConeQuotient : Cokernel (chainOfCochain (mappingCone φ)) 0 →ₗ[R] L :=
  (rawConeQuotient φ p hex).comp (cochainCokernelLinearEquiv (mappingCone φ)).toLinearMap

theorem rawConeQuotient_inr :
    (rawConeQuotient φ p hex).comp (cochainCokernelMap (mappingCone.inr φ)) = p := by
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := (LinearMap.range (G.d (-1) 0).hom).mkQ_surjective z
  change p (Submodule.Quotient.mk
    ((coneTermEquiv φ 0 (((mappingCone.inr φ).f 0).hom x)).1)) = p (Submodule.Quotient.mk x)
  congr 2
  change (((mappingCone.inr φ).f 0 ≫ (mappingCone.snd φ).v 0 0 (add_zero 0)).hom x) = x
  simp

theorem completeConeQuotient_inr :
    (completeConeQuotient φ p hex).comp
      (cokernelMap (extendMap (mappingCone.inr φ) negIndexEmbedding) 0) =
      p.comp (cochainCokernelLinearEquiv G).toLinearMap := by
  unfold completeConeQuotient
  rw [LinearMap.comp_assoc, cochainCokernelLinearEquiv_natural,
    ← LinearMap.comp_assoc, rawConeQuotient_inr]

def mappingConeStableQuotient [Module.Injective R R]
    (hF : ExactProjectiveCochain F)
    (hi : Function.Injective (cochainCokernelMap φ)) (hp : Function.Surjective p) :
    StableIsomorphism R (Cokernel (chainOfCochain (mappingCone φ)) 0) L := by
  letI := hF.finite 1
  letI := hF.projective 1
  letI : Module.Injective R (F.X 1) := finiteProjective_injective
  exact (StableIsomorphism.ofLinearEquiv (completeConeBlockEquiv φ)).trans
    (ConeQuotientMap.stableIsomorphism (F.d (-1) 0).hom (F.d 0 1).hom
      (G.d (-1) 0).hom (φ.f 0).hom (cochainCokernelMap φ) p
      (rawCokernelMap_comm φ) hex hi
      (congrArg ModuleCat.Hom.hom (F.d_comp_d (-1) 0 1)) hp)

theorem mappingConeStableQuotient_hom [Module.Injective R R]
    (hF : ExactProjectiveCochain F)
    (hi : Function.Injective (cochainCokernelMap φ)) (hp : Function.Surjective p) :
    (mappingConeStableQuotient φ p hex hF hi hp).hom =
      StableHom.classOf R _ _ (completeConeQuotient φ p hex) := by
  change StableHom.comp
    (StableHom.classOf R _ _ (ConeQuotientMap.quotientMap _ _ _ _ _ _ _ _))
    (StableHom.classOf R _ _ (completeConeBlockEquiv φ).toLinearMap) = _
  rw [StableHom.comp_classOf]
  rfl

end ArExplicit

end

end OAI
