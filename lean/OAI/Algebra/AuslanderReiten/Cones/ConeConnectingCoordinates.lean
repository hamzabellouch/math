import OAI.Algebra.AuslanderReiten.Cones.MappingConeCokernel
import OAI.Algebra.AuslanderReiten.Stable.StableConnecting

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex CompleteComparison
universe u
variable {R : Type u} [Ring R]
variable (H : CochainComplex (ModuleCat.{u} R) ℤ)

abbrev RawSyzygy := H.X (-1) ⧸ LinearMap.range (H.d (-2) (-1)).hom

def rawSyzygyInclusion : RawSyzygy H →ₗ[R] H.X 0 :=
  (LinearMap.range (H.d (-2) (-1)).hom).liftQ (H.d (-1) 0).hom
    (LinearMap.range_le_ker_iff.mpr (congrArg ModuleCat.Hom.hom (H.d_comp_d (-2) (-1) 0)))

theorem rawSyzygyInclusion_cover :
    ((LinearMap.range (H.d (-1) 0).hom).mkQ).comp (rawSyzygyInclusion H) = 0 := by
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (H.d (-2) (-1)).hom) z
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨z, rfl⟩

variable {H} {F G : CochainComplex (ModuleCat.{u} R) ℤ}
variable (φ : F ⟶ G) (κ : H ⟶ mappingCone φ)

def coneLiftMiddle : H.X 0 →ₗ[R] CochainCokernel G :=
  (LinearMap.range (G.d (-1) 0).hom).mkQ.comp
    ((LinearMap.fst R _ _).comp ((coneTermEquiv φ 0).toLinearMap.comp (κ.f 0).hom))

def coneLiftKernelComponent : H.X (-1) →ₗ[R] CochainCokernel F :=
  (LinearMap.range (F.d (-1) 0).hom).mkQ.comp
    ((LinearMap.snd R _ _).comp ((conePreviousTermEquiv φ).toLinearMap.comp (κ.f (-1)).hom))

theorem coneLiftKernelComponent_square :
    (cochainCokernelMap φ).comp (coneLiftKernelComponent φ κ) =
      (coneLiftMiddle φ κ).comp (H.d (-1) 0).hom := by
  ext z
  have hκ := congrArg (fun f : H.X (-1) ⟶ (mappingCone φ).X 0 => f.hom z) (κ.comm (-1) 0)
  change ((mappingCone φ).d (-1) 0).hom ((κ.f (-1)).hom z) =
    (κ.f 0).hom ((H.d (-1) 0).hom z) at hκ
  have hc := DFunLike.congr_fun (coneTermEquiv_differential φ (-1)) ((κ.f (-1)).hom z)
  change coneTermEquiv φ 0 (((mappingCone φ).d (-1) 0).hom ((κ.f (-1)).hom z)) = _ at hc
  rw [hκ] at hc
  have hh := congrArg (fun v : G.X 0 × F.X 1 =>
    (LinearMap.range (G.d (-1) 0).hom).mkQ v.1) hc
  change (coneLiftMiddle φ κ) ((H.d (-1) 0).hom z) =
    (LinearMap.range (G.d (-1) 0).hom).mkQ
      ((G.d (-1) 0).hom (conePreviousTermEquiv φ ((κ.f (-1)).hom z)).1 +
        (φ.f 0).hom (conePreviousTermEquiv φ ((κ.f (-1)).hom z)).2) at hh
  have hz : (LinearMap.range (G.d (-1) 0).hom).mkQ
      ((G.d (-1) 0).hom (conePreviousTermEquiv φ ((κ.f (-1)).hom z)).1) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr ⟨_, rfl⟩
  rw [map_add, hz, zero_add] at hh
  exact hh.symm

variable (hi : Function.Injective (cochainCokernelMap φ))

include hi in

theorem coneLiftKernelComponent_closed :
    (coneLiftKernelComponent φ κ).comp (H.d (-2) (-1)).hom = 0 := by
  ext z
  apply hi
  change ((cochainCokernelMap φ).comp (coneLiftKernelComponent φ κ))
    ((H.d (-2) (-1)).hom z) = cochainCokernelMap φ 0
  rw [map_zero]
  rw [coneLiftKernelComponent_square]
  change (coneLiftMiddle φ κ)
    (((H.d (-1) 0).hom.comp (H.d (-2) (-1)).hom) z) = 0
  rw [show (H.d (-1) 0).hom.comp (H.d (-2) (-1)).hom = 0 from
    congrArg ModuleCat.Hom.hom (H.d_comp_d (-2) (-1) 0)]
  exact map_zero _

def coneLiftKernel : RawSyzygy H →ₗ[R] CochainCokernel F :=
  (LinearMap.range (H.d (-2) (-1)).hom).liftQ (coneLiftKernelComponent φ κ)
    (LinearMap.range_le_ker_iff.mpr (coneLiftKernelComponent_closed φ κ hi))

theorem coneLiftKernel_square :
    (cochainCokernelMap φ).comp (coneLiftKernel φ κ hi) =
      (coneLiftMiddle φ κ).comp (rawSyzygyInclusion H) := by
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (H.d (-2) (-1)).hom) z
  exact DFunLike.congr_fun (coneLiftKernelComponent_square φ κ) z

variable (p : CochainCokernel G →ₗ[R] CochainCokernel H)
variable (he : Function.Exact (cochainCokernelMap φ) p)

theorem coneLiftMiddle_square :
    p.comp (coneLiftMiddle φ κ) =
      ((rawConeQuotient φ p he).comp (cochainCokernelMap κ)).comp
        (LinearMap.range (H.d (-1) 0).hom).mkQ := by
  ext z
  rfl

end ArExplicit

end

end OAI
