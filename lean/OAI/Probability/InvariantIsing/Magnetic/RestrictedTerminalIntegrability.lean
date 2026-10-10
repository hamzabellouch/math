import OAI.Probability.InvariantIsing.Fields.VectorTerminalLabeled
import OAI.Probability.InvariantIsing.Fields.FieldEnergyCoordinates
import OAI.Probability.InvariantIsing.Magnetic.RestrictedFieldTerminal

namespace OAI

/-! Actual ordinary and constrained field terminals have integrable Gibbs weights. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal BigOperators
namespace InvariantIsing

theorem restrictedTerminal_exp_integrable_ae {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep) (z : Fin N → ℝ) :
    ∀ᵐ p ∂vectorTerminalCoordinateLaw N h.depth (chainExponent h.cut) (fieldStepVariance h),
      Integrable (fun α => Real.exp (restrictedFieldTerminal S
        (labeledEnergy h.depth (markForestOfCoords (Fin N → ℝ) h.depth p.2) α z)))
        (labeledLeafLaw h.depth p.1) := by
  filter_upwards [field_vector_spin_exp_integrable N hN h z] with p hp
  have hi := spinLeafTerminal_exp_integrable (labeledLeafLaw h.depth p.1)
    (fun s : Spin N × LabeledLeaf h.depth => Real.exp 0 * fieldEnergy (fieldVectorEndpoint N h p z s.2) s.1) (by simpa using hp)
  have hfull : Integrable (fun α => Real.exp (∑ j, Real.log (Real.cosh (fieldVectorEndpoint N h p z α j))))
      (labeledLeafLaw h.depth p.1) := by
    convert hi using 1
    funext α
    congr 1
    simp only [spinLeafTerminal,Real.exp_zero,one_mul]
    rw [finiteLogIntegral_uniformSpinPrior,logPartition_fieldEnergy]
  apply hfull.mono' (measurable_of_countable _).aestronglyMeasurable
  apply ae_of_all
  intro α
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (restrictedFieldTerminal_le_univ S hS _)

end InvariantIsing

end

end OAI
