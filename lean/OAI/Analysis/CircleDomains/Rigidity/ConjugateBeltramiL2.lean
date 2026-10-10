import OAI.Geometry.Cannon.Beltrami.MultiplyLp
import OAI.Analysis.CircleDomains.Rigidity.ConductivityContraction
import OAI.Analysis.CircleDomains.Sobolev.ComplexSobolevTransport

namespace OAI

/-! The actual Beurling operator in the physical plane. Its exact L2
isometry supplies the operator previously parameterized in conductivity
contraction; no second fixed-point argument is needed. -/
open MeasureTheory Filter
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

 def complexLpToPhysical : PlaneL2 →ₗᵢ[ℂ] ComplexPlaneL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ complexPlaneCoordinates complexPlaneCoordinates_measurePreserving

 def physicalLpToComplex : ComplexPlaneL2 →ₗᵢ[ℂ] PlaneL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ complexPlaneCoordinates.symm
    (complexPlaneCoordinates_measurePreserving.symm
      complexPlaneCoordinates.toHomeomorph.toMeasurableEquiv)

 def physicalBeurling : ComplexPlaneL2 →L[ℝ] ComplexPlaneL2 :=
  (complexLpToPhysical.toContinuousLinearMap.comp
    (beurling.comp physicalLpToComplex.toContinuousLinearMap)).restrictScalars ℝ

lemma physicalBeurling_norm (f : ComplexPlaneL2) : ‖physicalBeurling f‖ = ‖f‖ := by
  change ‖complexLpToPhysical (beurling (physicalLpToComplex f))‖ = ‖f‖
  rw [complexLpToPhysical.norm_map, norm_beurling, physicalLpToComplex.norm_map]

lemma complexLpToPhysical_coe (f : PlaneL2) :
    complexLpToPhysical f =ᵐ[volume] fun x => f (complexPlaneCoordinates x) :=
  Lp.coeFn_compMeasurePreserving f complexPlaneCoordinates_measurePreserving

lemma physicalLpToComplex_coe (f : ComplexPlaneL2) :
    physicalLpToComplex f =ᵐ[volume] fun z => f (complexPlaneCoordinates.symm z) :=
  Lp.coeFn_compMeasurePreserving f
    (complexPlaneCoordinates_measurePreserving.symm
      complexPlaneCoordinates.toHomeomorph.toMeasurableEquiv)

lemma physicalLpToComplex_complexLpToPhysical (f : PlaneL2) :
    physicalLpToComplex (complexLpToPhysical f) = f := by
  apply Lp.ext
  filter_upwards [physicalLpToComplex_coe (complexLpToPhysical f),
    (complexPlaneCoordinates_measurePreserving.symm
      complexPlaneCoordinates.toHomeomorph.toMeasurableEquiv).quasiMeasurePreserving.ae (complexLpToPhysical_coe f)]
    with z hz hw
  simpa only [hz, hw, ContinuousLinearEquiv.apply_symm_apply]

lemma physicalLpToComplex_beurling (f : ComplexPlaneL2) :
    physicalLpToComplex (physicalBeurling f) = beurling (physicalLpToComplex f) :=
  physicalLpToComplex_complexLpToPhysical _

lemma physicalBeurling_complex_coe (f : ComplexPlaneL2) :
    beurling (physicalLpToComplex f) =ᵐ[volume]
      fun z => physicalBeurling f (complexPlaneCoordinates.symm z) := by
  rw [← physicalLpToComplex_beurling]
  exact physicalLpToComplex_coe _

lemma exists_actual_conductivity_density (q : EuclideanPlane → ℝ)
    (hq : MemLp q 2 volume) (k : ℝ≥0) (hk : k < 1)
    (hb : ∀ᵐ x ∂volume, ‖q x‖ ≤ k) :
    ∃ g : ComplexPlaneL2,
      (∀ᵐ x ∂volume, g x = (q x : ℂ) * star (1 + physicalBeurling g x)) ∧
      ‖g‖ ≤ ‖conductivitySource q hq‖ / (1 - (k : ℝ)) :=
  exists_conductivity_density q hq k hk hb physicalBeurling
    (fun f => (physicalBeurling_norm f).le)

end CircleDomainRigidity

end

end OAI
