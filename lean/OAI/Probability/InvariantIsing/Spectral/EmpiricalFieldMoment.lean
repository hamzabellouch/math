import OAI.Probability.InvariantIsing.Spectral.EmpiricalSpectralLaw

namespace OAI

/-! Every finite empirical field law has all real-valued moments. -/
noncomputable section
open MeasureTheory
namespace InvariantIsing

lemma empiricalField_integrable {N : ℕ} (hN : 0 < N) (c : Fin N → ℝ) (f : ℝ → ℝ) :
    Integrable f (empiricalSpectralLaw hN c : Measure ℝ) := by
  change Integrable f (Measure.sum (fun i : Fin N => ENNReal.ofReal ((1 : ℝ)/N) • Measure.dirac (c i)))
  rw [Measure.sum_fintype]
  apply integrable_finsetSum_measure.mpr
  intro i _
  exact (integrable_dirac (by simp)).smul_measure (by finiteness)

end InvariantIsing

end

end OAI
