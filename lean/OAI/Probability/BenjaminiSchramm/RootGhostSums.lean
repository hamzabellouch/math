import OAI.Probability.BenjaminiSchramm.RootTiltedGhost

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E ι : Type*} [Countable V] [Countable E] [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] (G : BondGraph V E) (root : ι → V)

lemma rootQuarterGhostMagnetization_eq_sum (p : unitInterval) {h : ℝ} (hh : 0 ≤ h) :
    G.rootQuarterGhostMagnetization root p h = ∑ i, G.quarterGhostMagnetization p (root i) h := by
  have hI := integrable_ghostKernel (Measure.count.prod (G.law p))
    (fun z => (G.rootQuarterMass root z).toReal)
    (G.measurable_rootQuarterMass root).ennreal_toReal (fun _ => ENNReal.toReal_nonneg) hh
  unfold rootQuarterGhostMagnetization ghostMagnetization
  erw [integral_prod _ hI]
  rw [integral_fintype Integrable.of_finite]
  simp only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul]
  rfl

lemma rootQuarterGhostDerivative_eq_sum (p : unitInterval) {h : ℝ} (hh : 0 < h) :
    G.rootQuarterGhostDerivative root p h = ∑ i, G.quarterGhostDerivative p (root i) h := by
  have hI := (hasDerivAt_ghostMagnetization (Measure.count.prod (G.law p))
    (fun z => (G.rootQuarterMass root z).toReal)
    (G.measurable_rootQuarterMass root).ennreal_toReal (fun _ => ENNReal.toReal_nonneg) hh).1
  unfold rootQuarterGhostDerivative ghostMagnetizationDerivative
  erw [integral_prod _ hI]
  rw [integral_fintype Integrable.of_finite]
  simp only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul]
  rfl

end CriticalPercolation.BondGraph

end

end OAI
