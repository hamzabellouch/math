import OAI.Probability.InvariantIsing.Spectral.MeasureRBounds
import OAI.Probability.InvariantIsing.Haar.Rotation

namespace OAI

/-! The degenerate spectral law in the general approximation argument. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace InvariantIsing

@[simp] lemma measureR_dirac (a x : ℝ) : measureR (Measure.dirac a) a x = a := by
  have h := measureR_bounds_all (Measure.dirac a) (l := a) (e := a)
    (by simp only [ae_dirac_eq, Filter.eventually_pure, Set.mem_Icc]; exact ⟨le_rfl, le_rfl⟩) x
  exact le_antisymm h.2 h.1

@[simp] lemma measureVariational_dirac (a : ℝ) :
    variationalFunctional (measureR (Measure.dirac a) a) = ((a / 2 : ℝ) : EReal) := by
  have he : measureR (Measure.dirac a) a = fun _ => a := funext (measureR_dirac a)
  rw [he, variationalFunctional_constant]

/-- The scalar spectral case of the pressure formula, for arbitrary rotations. -/
theorem tendsto_pressure_scalar_variational
    (eig : (N : ℕ) → Fin (N + 1) → ℝ) (U : (N : ℕ) → Rotation (N + 1))
    (a : ℝ) (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (heig : ∀ N i, |eig N i - a| ≤ δ N) :
    Tendsto (fun N => rotatedPressure (eig N) (U N) (fun _ => 0)) atTop
      (𝓝 (variationalFunctional (measureR (Measure.dirac a) a)).toReal) := by
  simpa only [measureVariational_dirac, EReal.toReal_coe] using
    tendsto_pressure_scalar_spectrum eig U a δ hδ heig

end InvariantIsing

end

end OAI
