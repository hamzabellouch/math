import OAI.Geometry.SurfaceImmersion.Primitive.BoundaryProfileFrame
import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveNormalCoordinates
import OAI.Geometry.SurfaceImmersion.Primitive.UniformPrimitiveProfiles

namespace OAI

/-! The five Euclidean profiles used by the exact primitive determine the
canonical normal frame in the real surface coordinates. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open RealModes NormalFrame SurfaceJetCoordinates JetVelocityCoordinates
open SurfaceVelocityFamily.Loop

abbrev EuclideanBoundaryProfile := Fin 5 → Euclidean

def boundaryProfileMap : EuclideanBoundaryProfile →L[ℝ] BoundaryProfile :=
  ContinuousLinearMap.pi fun i =>
    spaceCoordinates.toContinuousLinearMap.comp (ContinuousLinearMap.proj i)

@[simp] lemma boundaryProfileMap_apply (J : EuclideanBoundaryProfile) (i : Fin 5) :
    boundaryProfileMap J i = spaceCoordinates (J i) := rfl

private lemma directional_euclidean_chart {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (v : JetPolynomial.Base) :
    PeriodicExpansion.directionalMap (fun q => JetVelocityCoordinates.toEuclidean (F (baseEquiv q))) v =
      fun q => JetVelocityCoordinates.toEuclidean (SmallModes.coordDeriv (baseEquiv v) F (baseEquiv q)) := by
  funext q
  change fderiv ℝ ((JetVelocityCoordinates.toEuclidean ∘ F) ∘ baseEquiv) q v = _
  rw [fderiv_comp q ((JetVelocityCoordinates.toEuclidean.contDiff.comp hF).differentiable (by simp) _)
    baseEquiv.differentiableAt,ContinuousLinearMap.comp_apply,baseEquiv.fderiv]
  rw [fderiv_comp (baseEquiv q) JetVelocityCoordinates.toEuclidean.differentiableAt
    (hF.differentiable (by simp) _),ContinuousLinearMap.comp_apply,JetVelocityCoordinates.toEuclidean.fderiv]
  rfl

lemma boundaryProfileMap_chart {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (z : ℝ) (p : JetPolynomial.Base) :
    boundaryProfileMap (primitiveJetProfile (fun q => JetVelocityCoordinates.toEuclidean (F (baseEquiv q))) z p) =
      realBoundaryProfile F z (baseEquiv p) := by
  have hfirst (v : JetPolynomial.Base) := directional_euclidean_chart hF v
  have hsecond (v w : JetPolynomial.Base) :
      PeriodicExpansion.directionalMap
        (PeriodicExpansion.directionalMap (fun q => JetVelocityCoordinates.toEuclidean (F (baseEquiv q))) v) w =
      fun q => JetVelocityCoordinates.toEuclidean (SmallModes.coordDeriv (baseEquiv w)
        (SmallModes.coordDeriv (baseEquiv v) F) (baseEquiv q)) := by
    rw [hfirst]
    exact directional_euclidean_chart (contDiff_real_coordDeriv hF _) w
  funext j
  fin_cases j
  · change spaceCoordinates (PeriodicExpansion.directionalMap _ (JetPolynomial.coordinateVector 0) p) = _
    rw [hfirst]
    simp only [baseEquiv_zero,JetVelocityCoordinates.toEuclidean,ContinuousLinearEquiv.apply_symm_apply]
    rfl
  · change spaceCoordinates (PeriodicExpansion.directionalMap _ (JetPolynomial.coordinateVector 1) p) = _
    rw [hfirst]
    simp only [baseEquiv_one,JetVelocityCoordinates.toEuclidean,ContinuousLinearEquiv.apply_symm_apply]
    rfl
  · change spaceCoordinates (PeriodicExpansion.directionalMap
      (PeriodicExpansion.directionalMap _ (JetPolynomial.coordinateVector 1))
      (JetPolynomial.coordinateVector 1) p) = _
    rw [hsecond]
    simp only [baseEquiv_one,JetVelocityCoordinates.toEuclidean,ContinuousLinearEquiv.apply_symm_apply]
    rfl
  · change spaceCoordinates (PeriodicExpansion.directionalMap
      (PeriodicExpansion.directionalMap _ (JetPolynomial.coordinateVector 0))
      (JetPolynomial.coordinateVector 1) p) = _
    rw [hsecond]
    simp only [baseEquiv_zero,baseEquiv_one,JetVelocityCoordinates.toEuclidean,
      ContinuousLinearEquiv.apply_symm_apply]
    exact real_second_coordDeriv_comm hF (baseEquiv p) SmallModes.dy SmallModes.dx
  · change spaceCoordinates (z • PeriodicExpansion.directionalMap
      (PeriodicExpansion.directionalMap _ (JetPolynomial.coordinateVector 0))
      (JetPolynomial.coordinateVector 0) p) = _
    rw [hsecond,map_smul]
    simp only [baseEquiv_zero,JetVelocityCoordinates.toEuclidean,ContinuousLinearEquiv.apply_symm_apply]
    rfl

/-- Transfer the exact primitive's Euclidean error directly into the normal
frame and all four second-form coefficients. -/
theorem compact_euclidean_boundary_stability {K : Set EuclideanBoundaryProfile}
    (hK : IsCompact K) (hregular : ∀ J ∈ K, boundaryProfileMap J ∈ regularBoundaryProfiles) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ J ∈ K, ∀ H : EuclideanBoundaryProfile, ‖H-J‖ ≤ δ →
        boundaryProfileMap H ∈ regularBoundaryProfiles ∧
        ‖profileGeometry (boundaryProfileMap H)-profileGeometry (boundaryProfileMap J)‖ < ε := by
  intro ε hε
  obtain ⟨r,hr,hclose⟩ := compact_boundary_profile_stability
    (hK.image boundaryProfileMap.continuous)
    (by rintro _ ⟨J,hJ,rfl⟩; exact hregular J hJ) ε hε
  let C := ‖boundaryProfileMap‖
  have hC : 0 ≤ C := norm_nonneg _
  refine ⟨r/(2*(C+1)),div_pos hr (by positivity),?_⟩
  intro J hJ H hHJ
  apply hclose (boundaryProfileMap J) (mem_image_of_mem boundaryProfileMap hJ)
  rw [← map_sub]
  calc
    ‖boundaryProfileMap (H-J)‖ ≤ C*‖H-J‖ := boundaryProfileMap.le_opNorm _
    _ ≤ C*(r/(2*(C+1))) := mul_le_mul_of_nonneg_left hHJ hC
    _ < r := by
      have hp : 0 < 2*(C+1) := by positivity
      rw [← mul_div_assoc]
      apply (div_lt_iff₀ hp).mpr
      nlinarith

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
