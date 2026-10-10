import Mathlib
import OAI.Analysis.Conductivity.Sources.AngularPhysicalTest
import OAI.Analysis.Conductivity.Sources.FaceIntegral
import OAI.Analysis.Conductivity.Variational.PhysicalFaceSum
import OAI.Analysis.Conductivity.Geometry.AffineCylinderIntegral
import OAI.Analysis.Conductivity.Sources.FacePasting
import OAI.Analysis.Conductivity.Sources.FluxCylinder

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory UnitAddTorus Matrix
open scoped ENNReal
local instance attachedPeriodicFluxMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance attachedPeriodicFluxIsProbabilityMeasure : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma inverseTranspose_flux_pair (A : Mat3) (hA : A.det≠0) (v w : Coord3) :
    (A⁻¹ᵀ*ᵥv) ⬝ᵥ(A*ᵥw)=v ⬝ᵥw := by
  rw [dotProduct_comm,Matrix.dotProduct_transpose_mulVec,Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA),Matrix.one_mulVec]

def attachedPeriodicFluxFace (F : Coord3 → Coord3) (a b : ℝ) (i j : Fin 4)
    (y : Coord3) : Coord3 :=
  let x := sourceCollarInverse i j y
  (|a| *sourceFlatDensity i j x) • ((attachedCartesianMatrix a i j x)⁻¹ᵀ*ᵥ
    F (flatEndCoordinates a b (sourceFaceAngles i j x)))

def attachedPeriodicFlux (F : Coord3 → Coord3) (a b : ℝ) : Coord3 → Coord3 :=
  sourceFacePaste (attachedPeriodicFluxFace F a b) 0

lemma attachedPeriodicFlux_open (F : Coord3 → Coord3) (a b : ℝ)
    (i j : Fin 4) {x : Coord3} (hx : x∈sourceCollarOpenBox) :
    attachedPeriodicFlux F a b (sourceCollarPiece i j x)=
      (|a| *sourceFlatDensity i j x) • ((attachedCartesianMatrix a i j x)⁻¹ᵀ*ᵥ
        F (flatEndCoordinates a b (sourceFaceAngles i j x))) := by
  rw [attachedPeriodicFlux,sourceFacePaste_open _ _ i j hx]
  simp only [attachedPeriodicFluxFace,sourceCollarInverse_point i j hx]

lemma attachedPeriodicFlux_test_density {F : Coord3 → Coord3}
    (hp : AngularPeriodic (2*Real.pi) F) {a b : ℝ} (ha : a≠0)
    {φ : Coord3 → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ)
    (i j : Fin 4) {x : Coord3} (hx : x∈sourceCollarOpenBox) :
    |(sourceCollarJacobian i j x).det| *
      (attachedPeriodicFlux F a b (sourceCollarPiece i j x) ⬝ᵥ
        physicalTestCovector φ (sourceCollarPiece i j x))=
      (|a| *angularArea)*(sourceFaceWeight i j x*
        sourceFluxDensity F a⁻¹ b φ (affineEndCoordinates a b (sourceFaceParameter i j x))) := by
  rw [attachedPeriodicFlux_open F a b i j hx,
    ←attachedFlatTestCovector_transport φ ha i j (sourceCollarOpenBox_subset hx),smul_dotProduct,
    inverseTranspose_flux_pair _ (attachedCartesianMatrix_det_ne_zero ha i j (sourceCollarOpenBox_subset hx))]
  have hp' : torusPeriodicDescent F (affineEndCoordinates a b (sourceFaceParameter i j x))=
      F (flatEndCoordinates a b (sourceFaceAngles i j x)) := by
    simpa only [flatEndCoordinates_axial,flatEndCoordinates_angles,affineEndCoordinates,
      Prod.map_apply,affineEndTime,id_eq,sourceFaceParameter,show sourceFaceAngles i j x 0=x 0 from rfl] using
      torusPeriodicDescent_angles hp (flatEndCoordinates a b (sourceFaceAngles i j x))
  simp only [sourceFluxDensity,hp']
  have hj := sourceAngularJet_attachedCovector hφ ha b i j hx
  change (fun k : Fin 3 => (sourceAngularJet φ a⁻¹ b k.succ
    (affineEndCoordinates a b (sourceFaceParameter i j x))).re)=attachedFlatTestCovector φ a i j x at hj
  rw [hj,smul_eq_mul,sourceFlatDensity,sourceFaceWeight,sourceFaceAngleMatrix_det]
  field_simp [abs_ne_zero.mpr (sourceCollarJacobian_extended_ne_zero i j (sourceCollarOpenBox_subset hx))]

theorem attachedPeriodicFlux_smooth_pullback {F : Coord3 → Coord3} (hF : Continuous F)
    (hp : AngularPeriodic (2*Real.pi) F) {φ : Coord3 → ℝ}
    (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) {a b l r R : ℝ} (ha : a≠0)
    (hlr : l≤r) (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R) :
    IntegrableOn (fun y => attachedPeriodicFlux F a b y ⬝ᵥphysicalTestCovector φ y)
      (sourceClosedCollarBand l r) volume ∧
    (∫ y in sourceClosedCollarBand l r,attachedPeriodicFlux F a b y ⬝ᵥphysicalTestCovector φ y)=
      |a| *angularArea*(∫ z,sourceFluxDensity F a⁻¹ b φ (affineEndCoordinates a b z)
        ∂(volume.restrict (Ioc l r)).prod volume) := by
  let H := sourceFluxDensity F a⁻¹ b φ
  let G := fun y => attachedPeriodicFlux F a b y ⬝ᵥphysicalTestCovector φ y
  have hH := (sourceFluxDensity_cylinder hF hp a⁻¹ b R hφ).1
  have hg := integrable_affineEndCoordinates ha hT hH
  have he (i j : Fin 4) :
      (fun x => |(sourceCollarDerivative i j x).det| • G (sourceCollarPiece i j x))=ᵐ[
        volume.restrict (sourceExtendedBox l r)]
      (fun x => (|a| *angularArea)*(sourceFaceWeight i j x*
        H (affineEndCoordinates a b (sourceFaceParameter i j x)))) := by
    filter_upwards [sourceExtendedBox_open_ae hl hr] with x hx
    dsimp only [G,H]
    rw [smul_eq_mul,sourceCollarDerivative_det,←sourceCollarJacobian_det]
    exact attachedPeriodicFlux_test_density hp ha hφ i j hx
  have hi (i j : Fin 4) : IntegrableOn G
      (sourceCollarPiece i j '' sourceExtendedBox l r) volume := by
    apply (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume measurableSet_Icc
      (fun x _ => (sourceCollarPiece_hasFDeriv i j x).hasFDerivWithinAt)
      (sourceExtendedBox_injOn i j hl hr) G).mpr
    exact ((integrable_sourceFacePullback hlr hg i j).const_mul (|a| *angularArea)).congr (he i j).symm
  have hG : IntegrableOn G (sourceClosedCollarBand l r) volume := by
    unfold IntegrableOn
    rw [sourceClosedCollarBand_measure_faces hl hr]
    exact integrable_finsetSum_measure.mpr (fun i _ =>
      integrable_finsetSum_measure.mpr fun j _ => hi i j)
  refine ⟨hG,?_⟩
  change (∫ y in sourceClosedCollarBand l r,G y)=_
  rw [integral_sourceClosedCollarBand_faces hl hr hG,
    integral_sourceCylinder_faces (F:=fun z => sourceFluxDensity F a⁻¹ b φ
      (affineEndCoordinates a b z)) hlr hg,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [sourceExtended_integral i j hl hr G,integral_congr_ae (he i j),integral_const_mul]
  rfl

end ScalarConductivity

end
end

end OAI
