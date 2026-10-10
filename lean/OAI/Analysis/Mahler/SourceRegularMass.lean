import OAI.Analysis.Mahler.SourceRegularLimit
import OAI.Analysis.Mahler.MassLimit

namespace OAI

open Set MeasureTheory Filter MahlerStokes
open scoped Topology ENNReal
namespace Mahler
noncomputable section
variable {k N m : ℕ} {U : Set (ComplexEuclidean (k+1))}
  {f : Fin N → ComplexEuclidean (k+1) → ℂ} {G : Fin N → MvPolynomial (Fin (k+1)) ℂ}

theorem source_integral_le_massBelow (h : MassHypotheses (k+1) N m U f G) (R : ℝ) :
    ENNReal.ofReal (∫ z in U ∩ {z | tau f z < R}, massDensity f z) ≤ massBelow U f R := by
  let D := U ∩ {z | tau f z < R}
  have hc : ContinuousOn (tau f) U := fun z hz => (h.contDiffAt_tau hz 0).continuousAt.continuousWithinAt
  have hD : IsOpen D := hc.isOpen_inter_preimage h.open_domain isOpen_Iio
  by_cases hi : IntegrableOn (massDensity f) D
  · have hp : 0 ≤ᵐ[volume.restrict D] massDensity f :=
      ae_restrict_of_forall_mem hD.measurableSet (fun z hz => h.massDensity_nonneg hz.1)
    exact le_of_eq (ofReal_integral_eq_lintegral_ofReal hi hp)
  · rw [integral_undef hi, ENNReal.ofReal_zero]
    exact bot_le

theorem source_regular_massBelow_of_flux_limit (h : MassHypotheses (k+1) N m U f G)
    {R L : ℝ} (hR : 0 < R) (hR1 : R < 1)
    (hreg : ∀ z ∈ U, tau f z = R → fderiv ℝ (tau f) z ≠ 0)
    (hlimit : Tendsto
      (fun r => sphereFlux r (sourceCoordinateForm (sourceCoordinates k) (logTau f) k))
      (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    ENNReal.ofReal (R^(k+1) * L) ≤ massBelow U f R :=
  (ENNReal.ofReal_le_ofReal (source_regular_mass_lower_of_flux_limit h hR hR1 hreg hlimit)).trans
    (source_integral_le_massBelow h R)

end
end Mahler

end OAI
