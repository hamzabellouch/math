import Mathlib
import OAI.Analysis.Conductivity.Fourier.AttachedPeriodicFlux

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory UnitAddTorus Matrix
open scoped ENNReal
local instance attachedPeriodicGreenMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance attachedPeriodicGreenIsProbabilityMeasure : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem attachedPeriodicFlux_smooth_green {F : Coord3 → Coord3}
    (hF : ContDiff ℝ 1 F) (hp : AngularPeriodic (2*Real.pi) F)
    {φ : Coord3 → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ)
    {a b l r R : ℝ} (ha : a≠0) (hlr : l≤r) (hR : 0≤R)
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R)
    (he : (0<a ∧ a*(l-b)=0 ∧ a*(r-b)=R) ∨
      (a<0 ∧ a*(l-b)=R ∧ a*(r-b)=0))
    (hd : ∀ x,x 0∈Icc 0 R → coordinateDivergence F x=0) :
    IntegrableOn (fun y => attachedPeriodicFlux F a b y ⬝ᵥphysicalTestCovector φ y)
      (sourceClosedCollarBand l r) volume ∧
    (∫ y in sourceClosedCollarBand l r,attachedPeriodicFlux F a b y ⬝ᵥphysicalTestCovector φ y)=
      angularArea*((∫ θ,torusPeriodicDescent F (R,θ) 0*
          φ (sourceAngularCollar (a⁻¹*R+b) θ))-
        (∫ θ,torusPeriodicDescent F (0,θ) 0*φ (sourceAngularCollar b θ))) := by
  obtain ⟨hi,hiE⟩ := attachedPeriodicFlux_smooth_pullback hF.continuous hp hφ ha hlr hl hr hT
  refine ⟨hi,hiE.trans ?_⟩
  have hI := (sourceFluxDensity_cylinder hF.continuous hp a⁻¹ b R hφ).1
  have hj : |a| *(∫ z,sourceFluxDensity F a⁻¹ b φ (affineEndCoordinates a b z)
      ∂(volume.restrict (Ioc l r)).prod volume)=
      ∫ z,sourceFluxDensity F a⁻¹ b φ z ∂(FiniteAxisMeasure R).prod volume := by
    rcases he with ⟨h,he₀,heR⟩|⟨h,heR,he₀⟩
    · exact integral_affineEndCoordinates_pos h hlr hT he₀ heR hR hI
    · exact integral_affineEndCoordinates_neg h hlr hT heR he₀ hR hI
  rw [mul_comm |a| angularArea,mul_assoc,hj,sourceFluxDensity_green hF hp hR hd a⁻¹ b hφ]

end ScalarConductivity

end
end

end OAI
