import OAI.Probability.InvariantIsing.Magnetic.RestrictedRotationLogMean
import OAI.Probability.InvariantIsing.Cavity.CavityOrientationProbability
import OAI.Probability.InvariantIsing.Cavity.CavityLogCovariance
import OAI.Probability.InvariantIsing.Cavity.CavityHaarSides

namespace OAI

/-! The orientation correction preserves the expected logarithmic
partition, not only the normalized Gibbs law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma restricted_orientation_log_mean {N m depth : ℕ} (hN : 0<N)
    (S : Finset (Spin N)) (hS : S.Nonempty)
    (V : Orthogonal N) (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) :
    restrictedRotationLogMean S hS T eig I u
      ((cavitySpecialOrthogonal (cavityOrientationLift hN V))⁻¹) =
      restrictedRotationLogMean S hS T eig I u V⁻¹ := by
  unfold restrictedRotationLogMean
  simp only [inv_inv]
  unfold cavityRotationHamiltonian
  simp only [show matrixRotation (cavitySpecialOrthogonal (cavityOrientationLift hN V)) =
    specialRotation (cavityOrientationLift hN V) from rfl, cavityOrientationLift_energy]
  exact cavity_log_partition_same_covariance _ _ _ _
    (fun x y => cavityOrientationLift_perturbation_covariance hN V I u x y)

theorem restricted_orientation_haar_log_mean {N m depth : ℕ} (hN : 0<N)
    (S : Finset (Spin N)) (hS : S.Nonempty)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (T : LabeledTree depth) (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) :
    (∫ V, restrictedRotationLogMean S hS T eig I u
      ((cavitySpecialOrthogonal (cavityOrientationLift hN V))⁻¹) ∂μ) =
      ∫ V, restrictedRotationLogMean S hS T eig I u V ∂μ := by
  simp_rw [restricted_orientation_log_mean hN S hS]
  rw [← integral_map (μ := μ) measurable_inv.aemeasurable
    (measurable_restrictedRotationLogMean S hS T eig I u).aestronglyMeasurable,
    ← Measure.inv_def, ← cavity_right_probability_inv_eq μ]

end InvariantIsing

end

end OAI
