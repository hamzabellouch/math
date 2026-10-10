import OAI.Probability.InvariantIsing.Cavity.CavityOrientationLog

namespace OAI

/-! The physical and namespaced tensor models have the same expected
logarithmic partition, preserving the fixed rotation and cascade tree. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

theorem tensorLeaf_log_mean_law {N m k depth : ℕ}
    (U : Rotation N) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amp : Fin k → ℝ) (v : Fin (depth+1) → SpinTensorIndex I degree → ℝ≥0)
    (T : LabeledTree depth) (H : Spin N × LabeledLeaf depth → ℝ) :
    (∫ z, Real.log (∫ x, Real.exp (H x+cylinderField
      (tensorLeafCoefficients U I degree amp depth v x) z)
      ∂labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T) ∂gaussianCoordinates) =
    ∫ z, Real.log (∫ x, Real.exp (H x+cylinderField
      (tensorNamespacedCoefficients U I degree amp depth v x) z)
      ∂labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T) ∂gaussianCoordinates := by
  let X := Spin N × LabeledLeaf depth
  let ν := labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T
  let G := fun w : X → ℝ => Real.log (∫ x, Real.exp (H x+w x) ∂ν)
  have hm : Measurable (fun p : (X → ℝ) × X => Real.exp (H p.2+p.1 p.2)) := by
    apply measurable_from_prod_countable_left
    intro x
    exact ((measurable_pi_apply x : Measurable (fun w : X → ℝ => w x)).const_add (H x)).exp
  have hG : Measurable G := hm.stronglyMeasurable.integral_prod_right'.measurable.log
  have hA : Measurable (fun z x => cylinderField (tensorLeafCoefficients U I degree amp depth v x) z) :=
    Measurable.of_eval (fun x => measurable_cylinderField _)
  have hC : Measurable (fun z x => cylinderField (tensorNamespacedCoefficients U I degree amp depth v x) z) :=
    Measurable.of_eval (fun x => measurable_cylinderField _)
  change (∫ z, G (fun x => cylinderField (tensorLeafCoefficients U I degree amp depth v x) z)
    ∂gaussianCoordinates) = _
  rw [← integral_map hA.aemeasurable hG.aestronglyMeasurable,
    tensorNamespacedFields_law U I degree amp depth v,
    integral_map hC.aemeasurable hG.aestronglyMeasurable]

theorem cavity_rotation_tensor_log_mean {N m depth : ℕ}
    (U : SpecialOrthogonal N) (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) :
    cavityRotationLogMean T eig I u ((cavitySpecialOrthogonal U)⁻¹) =
      ∫ z, tensorNamespacedLog eig (fun _ => 0) I
        (fun j : Fin N => enumeratedSpectralDegree m j)
        (tensorPerturbationAmplitude N (fun j => u j)) depth
        (fun j : Fin N => enumeratedTreeDegree m j) (fun _ => 0) ((U,T),z)
        ∂gaussianCoordinates := by
  let degree := fun j : Fin N => enumeratedSpectralDegree m j
  let amp := tensorPerturbationAmplitude N (fun j : Fin N => u j)
  let v : Fin (depth+1) → SpinTensorIndex I degree → ℝ≥0 := fun i =>
    tensorPathProfile I degree depth (fun j : Fin N => enumeratedTreeDegree m j) (fun _ => 0) i
  have hh := tensorLeaf_log_mean_law (specialRotation U) I degree amp v T
    (fun x => rotatedEnergy eig (specialRotation U) x.1)
  have hr : matrixRotation (cavitySpecialOrthogonal U) = specialRotation U := rfl
  simp only [cavityRotationLogMean, inv_inv, hr, tensorNamespacedLog]
  unfold cavityRotationHamiltonian
  simp only [fieldEnergy, zero_mul, Finset.sum_const_zero, add_zero]
  simpa only [cavityPerturbationCoefficients, degree, amp, v] using hh

end InvariantIsing

end

end OAI
