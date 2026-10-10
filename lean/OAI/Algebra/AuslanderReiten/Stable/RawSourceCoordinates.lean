import OAI.Algebra.AuslanderReiten.Cones.ConeConnectingCoordinates
import OAI.Algebra.AuslanderReiten.Stable.SourceStableCoordinates

namespace OAI

noncomputable section
namespace ArExplicit.CompleteComparison
open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex
universe u
variable {R : Type u} [Ring R]
variable (K : CochainComplex (ModuleCat.{u} R) ℤ)

def rawSyzygyEquiv : Cokernel (chainOfCochain K) 1 ≃ₗ[R] RawSyzygy K :=
  cokernelLinearCongr _ _
    (K.extendXIso negIndexEmbedding (i := -2) (i' := 2) rfl).toLinearEquiv
    (K.extendXIso negIndexEmbedding (i := -1) (i' := 1) rfl).toLinearEquiv
    (congrArg ModuleCat.Hom.hom
      (reverseShortComplexIso K (-2) (-1) 0 2 1 0 rfl rfl rfl).hom.comm₁₂).symm

@[simp]
theorem rawSyzygyEquiv_symm_mk (z : K.X (-1)) :
    (rawSyzygyEquiv K).symm (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ((K.extendXIso negIndexEmbedding (i := -1) (i' := 1) rfl).inv.hom z) := rfl

variable {k : Type u} [Field k] [CharP k 2] [Algebra k R]
variable {K} {L : CochainComplex (ModuleCat.{u} R) ℤ}

def rawSourceCocycleMap (x : Cocycle K L 1) : RawSyzygy K →ₗ[R] CochainCokernel L :=
  (cochainCokernelLinearEquiv L).toLinearMap.comp
    ((sourceCocycleMap x).comp (rawSyzygyEquiv K).symm.toLinearMap)

include k in
@[simp]
theorem rawSourceCocycleMap_mk (x : Cocycle K L 1) (z : K.X (-1)) :
    rawSourceCocycleMap x (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ((x.val.v (-1) 0 rfl).hom z) := by
  change cochainCokernelLinearEquiv L
    (sourceCocycleMap x ((rawSyzygyEquiv K).symm (Submodule.Quotient.mk z))) = _
  rw [rawSyzygyEquiv_symm_mk, sourceCocycleMap_mk (k := k)]
  change Submodule.Quotient.mk
    ((L.extendXIso negIndexEmbedding (i := 0) (i' := 0) rfl).hom.hom
      ((sourceCocycleComponent x).hom
        ((K.extendXIso negIndexEmbedding (i := -1) (i' := 1) rfl).inv.hom z))) = _
  simp [sourceCocycleComponent]

variable {F G H : CochainComplex (ModuleCat.{u} R) ℤ}
variable (φ : F ⟶ G) (κ : H ⟶ mappingCone φ)

include k in

theorem rawSourceCocycleMap_cone (hi : Function.Injective (cochainCokernelMap φ)) :
    rawSourceCocycleMap (cocycleProduct (Cocycle.ofHom κ) (mappingCone.fst φ)) =
      coneLiftKernel φ κ hi := by
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (H.d (-2) (-1)).hom) z
  erw [rawSourceCocycleMap_mk (k := k)]
  change Submodule.Quotient.mk
    ((((Cochain.ofHom κ).comp (mappingCone.fst φ).val rfl).v (-1) 0 rfl).hom z) = _
  rw [Cochain.comp_v _ _ rfl (-1) (-1) 0 (by omega) (by omega), Cochain.ofHom_v]
  rfl

end ArExplicit.CompleteComparison

end

end OAI
