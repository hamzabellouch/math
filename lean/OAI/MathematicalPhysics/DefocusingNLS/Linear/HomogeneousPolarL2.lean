import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalDerivative
import Mathlib.MeasureTheory.Constructions.HaarToSphere

namespace OAI

/-! # The exact twelve-dimensional polar L² realization

The surface measure is the Haar-induced (unnormalized) sphere measure, and
its radial partner is r^11 dr.  This transfers the already constructed
physical derivatives, without making an additional regularity assumption.
-/

open MeasureTheory Set

namespace DefocusingNLS

abbrev PhysicalUnitSphere := Metric.sphere (0 : EuclideanSpace ℝ (Fin 12)) 1
abbrev PhysicalPositiveRadius := Ioi (0 : ℝ)

noncomputable def physicalSphereMeasure : Measure PhysicalUnitSphere :=
  (volume : Measure (EuclideanSpace ℝ (Fin 12))).toSphere

noncomputable def physicalRadiusMeasure : Measure PhysicalPositiveRadius :=
  Measure.volumeIoiPow 11

instance : IsFiniteMeasure physicalSphereMeasure := by
  unfold physicalSphereMeasure
  infer_instance

instance : SigmaFinite physicalRadiusMeasure := by
  unfold physicalRadiusMeasure
  infer_instance

noncomputable def physicalPolarMeasure : Measure (PhysicalUnitSphere × PhysicalPositiveRadius) :=
  physicalSphereMeasure.prod physicalRadiusMeasure

noncomputable def physicalPolarPoint (p : PhysicalUnitSphere × PhysicalPositiveRadius) :
    EuclideanSpace ℝ (Fin 12) := p.2.1 • p.1.1

/-- Polar coordinates preserve precisely the Cartesian volume measure. -/
theorem measurePreserving_physicalPolarPoint :
    MeasurePreserving physicalPolarPoint physicalPolarMeasure volume := by
  dsimp only [physicalPolarPoint, physicalPolarMeasure, physicalSphereMeasure, physicalRadiusMeasure]
  let E := EuclideanSpace ℝ (Fin 12)
  have hp := MeasurePreserving.symm (homeomorphUnitSphereProd E).toMeasurableEquiv
    (volume.measurePreserving_homeomorphUnitSphereProd (E := E))
  have hs := measurePreserving_subtype_coe
    (μa := (volume : Measure E)) (measurableSet_singleton (0 : E)).compl
  have h := hs.comp hp
  have hdim : Module.finrank ℝ E = 12 := by simp [E]
  change MeasurePreserving (fun p : Metric.sphere (0 : E) 1 × Ioi (0 : ℝ) =>
    p.2.1 • p.1.1) (volume.toSphere.prod (Measure.volumeIoiPow
      (Module.finrank ℝ E - 1))) (volume.restrict {0}ᶜ) at h
  rw [hdim] at h
  simp only [Nat.reduceSub, restrict_compl_singleton] at h
  exact h

/-- The pullback is a genuine L² isometry, including for nonsmooth completed data. -/
noncomputable def physicalPolarL2 :
    Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin 12))) →ₗᵢ[ℂ]
      Lp ℂ 2 physicalPolarMeasure :=
  Lp.compMeasurePreservingₗᵢ ℂ physicalPolarPoint measurePreserving_physicalPolarPoint

theorem physicalPolarL2_ae (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin 12)))) :
    physicalPolarL2 f =ᵐ[physicalPolarMeasure] fun p => f (physicalPolarPoint p) :=
  Lp.coeFn_compMeasurePreserving f measurePreserving_physicalPolarPoint

/-- Every Cartesian derivative from the homogeneous completion has an exact
sphere/radius L² representative with the same norm. -/
noncomputable def homogeneousPolarDerivative (a : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < (N : ℝ)) (j : Fin N → Fin 12) :
    HomogeneousY a N →L[ℂ] Lp ℂ 2 physicalPolarMeasure :=
  physicalPolarL2.toContinuousLinearMap.comp
    (homogeneousPhysicalDerivative a N ha ha1 hk j)

theorem homogeneousPolarDerivative_norm_le (a : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < (N : ℝ)) (j : Fin N → Fin 12)
    (u : HomogeneousY a N) :
    ‖homogeneousPolarDerivative a N ha ha1 hk j u‖ ≤ ‖u‖ := by
  change ‖physicalPolarL2 (homogeneousPhysicalDerivative a N ha ha1 hk j u)‖ ≤ _
  rw [physicalPolarL2.norm_map]
  exact homogeneousPhysicalDerivative_norm_le a N ha ha1 hk j u

end DefocusingNLS

end OAI
