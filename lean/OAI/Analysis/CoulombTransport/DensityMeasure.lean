import OAI.Analysis.CoulombTransport.Model

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

/-- Every measure obtained from a density is absolutely continuous with respect to volume. -/
theorem densityMeasure_absolutelyContinuous (rho : E3 → ℝ) :
    densityMeasure rho ≪ (volume : Measure E3) :=
  withDensity_absolutelyContinuous _ _

/-- A density measure has no point atoms, without any regularity assumption on the density. -/
instance densityMeasure_nullSingletonClass (rho : E3 → ℝ) :
    NullSingletonClass (densityMeasure rho) := by
  unfold densityMeasure
  infer_instance

/-- A density measure gives no mass to the complement of its topological support. -/
theorem densityMeasure_tsupport_compl (rho : E3 → ℝ) :
    densityMeasure rho (tsupport rho)ᶜ = 0 := by
  rw [densityMeasure, withDensity_apply _ (isClosed_tsupport rho).measurableSet.compl]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem (isClosed_tsupport rho).measurableSet.compl] with x hx
  simp only [Pi.zero_apply]
  rw [image_eq_zero_of_notMem_tsupport hx, ENNReal.ofReal_zero]

/-- Compact support of the density provides an explicit compact set of full measure. -/
theorem densityMeasure_exists_compact_conull {rho : E3 → ℝ}
    (hrho : HasCompactSupport rho) :
    ∃ K : Set E3, IsCompact K ∧ densityMeasure rho Kᶜ = 0 :=
  ⟨tsupport rho, hrho, densityMeasure_tsupport_compl rho⟩

end Problem356

end

end OAI
