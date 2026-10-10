import Mathlib
import OAI.Analysis.Conductivity.Variational.FullEndClosedEnergy
import OAI.Analysis.Conductivity.Sources.AngularPhysicalTest
import OAI.Analysis.Conductivity.Sources.FaceIntegral
import OAI.Analysis.Conductivity.Variational.PhysicalFaceSum
import OAI.Analysis.Conductivity.Sources.EndPointEnergy
import OAI.Analysis.Conductivity.Geometry.AffineCylinderIntegral

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus Matrix
open scoped ENNReal
local instance physicalEndSmoothEnergyMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalEndSmoothEnergyIsProbabilityMeasure : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem fullAttachedEnd_smooth_energy_pullback (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : spectralTraceGraph (torusRate s)) (κ : ℝ)
    {φ : (Fin 3 → ℝ) → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ)
    {a b l r R : ℝ} (ha : a≠0) (hlr : l≤r) (hR : 0≤R)
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R)
    (ht : ∀ t∈Ioo l r,0<a*(t-b)) :
    IntegrableOn (fun y => fullAttachedEndGradient s f a b κ y ⬝ᵥ
      (attachedCollarTensor s a y*ᵥphysicalTestCovector φ y)) (sourceClosedCollarBand l r) volume ∧
    (∫ y in sourceClosedCollarBand l r,fullAttachedEndGradient s f a b κ y ⬝ᵥ
      (attachedCollarTensor s a y*ᵥphysicalTestCovector φ y))=
      |a| *angularArea*(∫ z,sourceEndSmoothDensity s f κ a⁻¹ b φ
        (affineEndCoordinates a b z) ∂(volume.restrict (Ioc l r)).prod volume) := by
  let F := sourceEndSmoothDensity s f κ a⁻¹ b φ
  let G := fun y => fullAttachedEndGradient s f a b κ y ⬝ᵥ
    (attachedCollarTensor s a y*ᵥphysicalTestCovector φ y)
  have hF := (sourceEndSmoothDensity_cylinder s hs f κ a⁻¹ b R hR hφ).1
  have hg := integrable_affineEndCoordinates ha hT hF
  have he (i j : Fin 4) :
      (fun x => |(sourceCollarDerivative i j x).det| • G (sourceCollarPiece i j x))=ᵐ[
        volume.restrict (sourceExtendedBox l r)]
      (fun x => (|a| *angularArea)*(sourceFaceWeight i j x •
        F (affineEndCoordinates a b (sourceFaceParameter i j x)))) := by
    filter_upwards [sourceExtendedBox_open_ae hl hr,sourceExtendedBox_axial_strict_ae l r]
      with x hx hm
    dsimp only [G]
    rw [smul_eq_mul,sourceCollarDerivative_det,←sourceCollarJacobian_det,
      fullAttachedEnd_test_energy s hs f κ φ ha i j hx (ht (x 0) hm)]
    have hj := sourceAngularJet_attachedCovector hφ ha b i j hx
    change _=(|a| *angularArea)*(sourceFaceWeight i j x *
      (fullEndFlatCovector s f κ (a*(x 0-b)) (torusAngles (sourceFaceAngles i j x)) ⬝ᵥ
        (flatCylinderMatrix s*ᵥ(fun k : Fin 3 => (sourceAngularJet φ a⁻¹ b k.succ
          (a*(x 0-b),torusAngles (sourceFaceAngles i j x))).re))))
    rw [hj]
    unfold sourceFaceWeight
    ring
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
    integral_sourceCylinder_faces (F:=fun z => sourceEndSmoothDensity s f κ a⁻¹ b φ
      (affineEndCoordinates a b z)) hlr hg,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [sourceExtended_integral i j hl hr G,integral_congr_ae (he i j),integral_const_mul]

end ScalarConductivity

end
end

end OAI
