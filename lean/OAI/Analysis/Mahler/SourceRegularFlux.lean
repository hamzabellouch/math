import OAI.Analysis.Mahler.SourceCoordinateExterior
import OAI.Analysis.Mahler.SourceCanonicalMeasure
import OAI.Analysis.Mahler.SourceBoundaryIntegral

namespace OAI

open ContinuousAlternatingMap MahlerStokes Set MeasureTheory
open scoped Topology
namespace Mahler
noncomputable section
variable {k N m : ℕ} {U : Set (ComplexEuclidean (k+1))}
  {f : Fin N → ComplexEuclidean (k+1) → ℂ} {G : Fin N → MvPolynomial (Fin (k+1)) ℂ}

/-- The punctured Stokes inequality for the coordinate forms,
Hessian mass density, outward inner sphere, and ordinary complex volume.
Only the geometric inclusion of the small closed ball is a premise. -/
theorem source_regular_flux_le_mass (h : MassHypotheses (k+1) N m U f G)
    {R r : ℝ} (hR : 0 < R) (hR1 : R < 1)
    (hreg : ∀ z ∈ U, tau f z = R → fderiv ℝ (tau f) z ≠ 0)
    (hr : 0 < r)
    (hB : coordClosedBall ((2*k+1)+1) r ⊆
      regularSublevel ((sourceCoordinates k) ⁻¹' U) (fun x => tau f (sourceCoordinates k x)) R) :
    sphereFlux r (sourceCoordinateForm (sourceCoordinates k) (logTau f) k) ≤
      (R⁻¹)^(k+1) * (∫ z in U ∩ {z | tau f z < R}, massDensity f z) := by
  let D := regularSublevel ((sourceCoordinates k) ⁻¹' U)
    (fun x => tau f (sourceCoordinates k x)) R
  have hD : IsOpen D := isOpen_regularSublevel
    (h.open_domain.preimage (sourceCoordinates k).continuous)
    (h.contDiffOn_coordinateTau (sourceCoordinates k) 1).continuousOn
  have hs := source_punctured_scaled_extDeriv h k (sourceCoordinates k) hR hR1 hreg hr hB
  have hi : (∫ x in D,
      extDeriv (sourceCoordinateForm (sourceCoordinates k) (energy f) k) x
        (coordinateBasis ((2*k+1)+1))) =
      ∫ z in U ∩ {z | tau f z < R}, massDensity f z := by
    calc
      _ = ∫ x in D, massDensity f (sourceCoordinates k x) :=
        setIntegral_congr_fun hD.measurableSet (fun x hx => h.coordinate_energy_extDeriv hx.1)
      _ = _ := setIntegral_sourceCoordinates k (U ∩ {z | tau f z < R}) (massDensity f)
  have hp : 0 ≤ ∫ x in D \ coordClosedBall ((2*k+1)+1) r,
      extDeriv (sourceCoordinateForm (sourceCoordinates k) (logTau f) k) x
        (coordinateBasis ((2*k+1)+1)) := by
    apply integral_nonneg_of_ae
    apply ae_restrict_of_forall_mem (hD.measurableSet.diff (isCompact_coordClosedBall _ _).measurableSet)
    intro x hx
    apply h.coordinate_log_extDeriv_nonneg hx.1.1
    intro hz
    apply hx.2
    subst x
    change radiusSq (0 : Fin ((2*k+1)+1) → ℝ) ≤ r^2
    simpa [radiusSq] using sq_nonneg r
  change (R⁻¹)^(k+1) * (∫ x in D, _) - _ = _ at hs
  rw [hi] at hs
  exact sub_nonneg.mp (hs ▸ hp)

end
end Mahler

end OAI
