import OAI.AlgebraicGeometry.SurfaceCones.CanonicalConormal
import OAI.AlgebraicGeometry.SurfaceCones.RestrictionRank

namespace OAI

/-! Smoothness of the degree-zero homogeneous charts in the completed Cartier model. -/
noncomputable section
open _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry CategoryTheory
namespace SourcePullbackChart

lemma surfaceIota_toComplex (i : Fin 3) :
    surfaceIota i ≫ ExplicitCone.projectiveSurfaceToComplex =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (surfaceChart i))) :=
  SourceSymmetry.homogeneousAway_toComplex _ _

/-- Smoothness of the coefficient charts. -/
instance surfaceChart_smooth (i : Fin 3) : Algebra.Smooth ℂ (surfaceChart i) := by
  let := SourceSymmetry.projectiveSurface_smooth
  have h : Smooth (surfaceIota i ≫ ExplicitCone.projectiveSurfaceToComplex) := inferInstance
  rw [surfaceIota_toComplex,
    HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Smooth.{0})] at h
  exact RingHom.smooth_algebraMap.mp h

instance surfaceChart_noetherian (i : Fin 3) : IsNoetherianRing (surfaceChart i) :=
  Algebra.FiniteType.isNoetherianRing ℂ (surfaceChart i)

instance surfaceChart_regular (i : Fin 3) : IsRegularRing (surfaceChart i) := by
  apply isRegularRing_iff.mpr
  intro p hp
  let x : Spec (.of (surfaceChart i)) := ⟨p,hp⟩
  let := SourceSymmetry.projectiveSurface_regular (surfaceIota i x)
  let := IsRegularLocalRing.of_ringEquiv
    (asIso ((surfaceIota i).stalkMap x)).commRingCatIsoToRingEquiv
  exact IsRegularLocalRing.of_ringEquiv (Spec.stalkIso (.of (surfaceChart i)) x).commRingCatIsoToRingEquiv

/-- The finite normalization map respects the very same complex
structure used in the smoothness theorem. -/
lemma projectiveNormalization_toComplex :
    ExplicitCone.projectiveNormalization ≫ SourceZeroSections.planeScalar =
      ExplicitCone.projectiveSurfaceToComplex := by
  let C : ExplicitCone.projectiveSurface.OpenCover :=
    { I₀ := Fin 3
      X := fun i => Spec (.of (surfaceChart i))
      f := surfaceIota
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        refine ⟨?_, inferInstance⟩
        intro x
        have hx : x ∈ ⨆ i, (surfaceIota i).opensRange := by rw [surfaceIota_cover]; trivial
        obtain ⟨i,hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
        obtain ⟨y,hy⟩ := hi
        exact ⟨i,y,hy⟩ }
  apply C.hom_ext
  intro i
  exact (SourceZeroSections.surfaceIota_scalar i).trans (surfaceIota_toComplex i).symm

end SourcePullbackChart

end

/-! Regularity of the completed source along its exceptional surface, via its principal quotients. -/
noncomputable section
namespace SourcePullbackChart
open KummerSourceModel
attribute [local instance] integralSurfaceCommRing integralSurfaceSemiring
  integralPullbackCommRing integralPullbackSemiring pullbackBaseAlgebra surfaceOriginAlgebra
  completedPullbackModule completedPullbackAction completedPullbackSMul completedPullbackTower
  completedSurfaceModule completedSeriesModule completedSourceChartCommRing completedSourceChartSemiring
  completedSourceAlgebra

def completedSourcePrincipalQuotient (i : Fin 3) :
    (completedSourceChart i ⧸ Ideal.span {completedFiberParameter i}) ≃+* surfaceChart i :=
  (Ideal.quotientEquiv _ _ (RingEquiv.refl _) (by simp [completedZeroIdeal_eq])).trans
    (completedZeroQuotient i)

instance completedSourcePrincipalQuotient_regular (i : Fin 3) :
    IsRegularRing (completedSourceChart i ⧸ Ideal.span {completedFiberParameter i}) :=
  IsRegularRing.of_ringEquiv (completedSourcePrincipalQuotient i).symm

/-- At every point of the exceptional fiber the ambient completed
source local ring is regular. -/
lemma completedSource_regular_at_fiber (i : Fin 3) (p : Ideal (completedSourceChart i))
    [p.IsPrime] (hp : completedFiberParameter i ∈ p) :
    IsRegularLocalRing (Localization.AtPrime p) := by
  apply RegularCartierLocalization.regular_at_prime (completedFiberParameter i) _ p hp
  intro h
  have hh := completedFiberParameter_regular i
  rw [h] at hh
  exact one_ne_zero (hh (by simp : (0 : completedSourceChart i) • (1 : completedSourceChart i) =
    (0 : completedSourceChart i) • (0 : completedSourceChart i)))

end SourcePullbackChart

end

end OAI
