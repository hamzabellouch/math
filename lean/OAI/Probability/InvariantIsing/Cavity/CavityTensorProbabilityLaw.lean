import OAI.Probability.InvariantIsing.Cavity.CavityRotationArray
import OAI.Probability.InvariantIsing.Arrays.NSpinTensorFrozen
import OAI.Probability.InvariantIsing.Arrays.TensorDiagonalCGF

namespace OAI

/-! The actual base Gibbs probability has the same Gaussian law as the
namespaced tensor realization used by the proved GG and Ward estimates. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

theorem tensorLeaf_gibbsProbability_law {N m k depth : ℕ}
    (U : Rotation N) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amp : Fin k → ℝ) (v : Fin (depth+1) → SpinTensorIndex I degree → ℝ≥0)
    (T : LabeledTree depth) (H : Spin N × LabeledLeaf depth → ℝ) :
    gaussianCoordinates.map (fun z => gibbsProbability
      (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T)
      (fun x => H x+cylinderField (tensorLeafCoefficients U I degree amp depth v x) z)) =
    gaussianCoordinates.map (fun z => gibbsProbability
      (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T)
      (fun x => H x+cylinderField (tensorNamespacedCoefficients U I degree amp depth v x) z)) := by
  let X := Spin N × LabeledLeaf depth
  let ν : Measure X := labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T
  let G : (X → ℝ) → Measure X := fun f => gibbsProbability ν (fun x => H x+f x)
  have hm : Measurable (fun p : (X → ℝ) × X => H p.2+p.1 p.2) := by
    apply measurable_from_prod_countable_left
    intro x
    exact (measurable_pi_apply x : Measurable (fun w : X → ℝ => w x)).const_add (H x)
  have hG : Measurable G := measurable_gibbsProbability (ν := fun _ => ν) measurable_const hm
  have hA : Measurable (fun z x => cylinderField (tensorLeafCoefficients U I degree amp depth v x) z) :=
    Measurable.of_eval (fun x => measurable_cylinderField _)
  have hC : Measurable (fun z x => cylinderField (tensorNamespacedCoefficients U I degree amp depth v x) z) :=
    Measurable.of_eval (fun x => measurable_cylinderField _)
  have hh := congrArg (fun μ : Measure (X → ℝ) => μ.map G)
    (tensorNamespacedFields_law U I degree amp depth v)
  simpa only [Measure.map_map hG hA, Measure.map_map hG hC, Function.comp_def, G] using hh

theorem cavity_rotation_tensor_probability_law {N m depth : ℕ}
    (U : SpecialOrthogonal N) (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) :
    gaussianCoordinates.map (fun z => cavityRotationProbability eig I u
      (((cavitySpecialOrthogonal U)⁻¹,T),z)) =
    gaussianCoordinates.map (fun z => tensorNamespacedReference eig (fun _ => 0) I
      (fun j : Fin N => enumeratedSpectralDegree m j)
      (tensorPerturbationAmplitude N (fun j => u j)) depth
      (fun j : Fin N => enumeratedTreeDegree m j) (fun _ => 0) ((U,T),z)) := by
  let degree := fun j : Fin N => enumeratedSpectralDegree m j
  let amp := tensorPerturbationAmplitude N (fun j : Fin N => u j)
  let v : Fin (depth+1) → SpinTensorIndex I degree → ℝ≥0 := fun i => tensorPathProfile I degree depth
    (fun j : Fin N => enumeratedTreeDegree m j) (fun _ => 0) i
  have hh := tensorLeaf_gibbsProbability_law (specialRotation U) I degree amp v T
    (fun x => rotatedEnergy eig (specialRotation U) x.1)
  have hr : matrixRotation (cavitySpecialOrthogonal U) = specialRotation U := rfl
  simp only [cavityRotationProbability, inv_inv, hr, tensorNamespacedReference]
  unfold cavityRotationHamiltonian tensorNamespacedHamiltonian
  simp only [fieldEnergy, zero_mul, Finset.sum_const_zero, add_zero]
  simpa only [cavityPerturbationCoefficients, degree, amp, v] using hh

end InvariantIsing

end

end OAI
