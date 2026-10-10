import OAI.Probability.InvariantIsing.Magnetic.RestrictedSpinPrior
import OAI.Probability.InvariantIsing.Fields.FieldEnergyCoordinates

namespace OAI

/-! The normalized constrained prior inherits the actual finite-field
exponential moments from the full spin prior. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma restrictedSpinPrior_eq_cond {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty) :
    (restrictedSpinPrior S hS : Measure (Spin N)) = cond (uniformSpinPrior N : Measure (Spin N)) S := by
  change cond (gibbsProbability (uniformSpinPrior N : Measure (Spin N)) (fun _ => 0)) S = _
  rw [gibbsProbability_eq_tilted _ _ Integrable.of_finite, tilted_const]

lemma integrable_restrictedSpinPrior_prod {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty)
    {X : Type*} [MeasurableSpace X] (ν : Measure X) [SFinite ν]
    {f : Spin N × X → ℝ} (hf : Integrable f ((uniformSpinPrior N : Measure (Spin N)).prod ν)) :
    Integrable f ((restrictedSpinPrior S hS : Measure (Spin N)).prod ν) := by
  have hzero : gibbsProbability (uniformSpinPrior N : Measure (Spin N)) (fun _ => 0) =
      (uniformSpinPrior N : Measure (Spin N)) := by
    rw [gibbsProbability_eq_tilted _ _ Integrable.of_finite, tilted_const]
  have hm : (uniformSpinPrior N : Measure (Spin N)) S ≠ 0 := by
    apply (measureReal_ne_zero_iff).mp
    have hp := spinGibbs_mass_pos (fun _ => 0) S hS
    rw [hzero] at hp
    exact hp.ne'
  rw [restrictedSpinPrior_eq_cond, ProbabilityTheory.cond, Measure.prod_smul_left]
  have he : ((uniformSpinPrior N : Measure (Spin N)).restrict S).prod ν =
      ((uniformSpinPrior N : Measure (Spin N)).prod ν).restrict ((S : Set (Spin N)) ×ˢ univ) := by
    conv_lhs => rw [← Measure.restrict_univ (μ := ν)]
    exact Measure.prod_restrict _ _
  rw [he]
  exact hf.restrict.smul_measure (ENNReal.inv_ne_top.mpr hm)

lemma restricted_field_vector_spin_exp_integrable {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep) (z : Fin N → ℝ) :
    ∀ᵐ p ∂fieldVectorCoordinateLaw N h,
      Integrable (fun s : Spin N × LabeledLeaf h.depth =>
        Real.exp (fieldEnergy (fieldVectorEndpoint N h p z s.2) s.1))
        ((restrictedSpinPrior S hS : Measure (Spin N)).prod (labeledLeafLaw h.depth p.1)) := by
  filter_upwards [field_vector_spin_exp_integrable N hN h z] with p hp
  exact integrable_restrictedSpinPrior_prod S hS _ hp

end InvariantIsing

end

end OAI
