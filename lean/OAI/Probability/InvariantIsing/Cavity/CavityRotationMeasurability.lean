import OAI.Probability.InvariantIsing.Cavity.CavityGroupGibbsInvariant

namespace OAI

/-! Joint measurability of the actual Gaussian Hamiltonian in an
orthogonal eigenbasis, the disorder and the spin/leaf state. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Matrix

namespace InvariantIsing

lemma measurable_cavityRotation_eval {N : ℕ} (x : EuclideanSpace ℝ (Fin N)) (i : Fin N) :
    Measurable (fun V : Orthogonal N => matrixRotation V⁻¹ x i) := by
  change Measurable (fun V : Orthogonal N => ∑ j, (V : Matrix (Fin N) (Fin N) ℝ) j i * x j)
  have hm : Measurable (fun V : Orthogonal N => (V : Matrix (Fin N) (Fin N) ℝ)) :=
    measurable_subtype_coe
  apply Finset.measurable_sum
  intro j _
  exact ((measurable_pi_apply i).comp ((measurable_pi_apply j).comp hm)).mul_const _

lemma measurable_cavityRotation_spinTensor {N m k : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (σ : Spin N) (i : SpinTensorIndex I degree) :
    Measurable (fun V : Orthogonal N =>
      spinTensorFeature (matrixRotation V⁻¹) I degree amplitude σ i) := by
  cases i with
  | inl i => exact measurable_const
  | inr v =>
    apply Measurable.const_mul
    unfold spectralMonomialFeature tensorFeature spectralSpinFeature
    apply Finset.measurable_prod
    intro a _
    apply Finset.measurable_prod
    intro j _
    exact (measurable_cavityRotation_eval (spinVector σ) (v.2 a j)).div_const _

lemma measurable_cavityRotation_perturbation {N m depth : ℕ}
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) (x : Spin N × LabeledLeaf depth) :
    Measurable (fun p : Orthogonal N × (ℕ → ℝ) =>
      cylinderField (cavityPerturbationCoefficients (matrixRotation p.1⁻¹) I u depth x) p.2) := by
  simp only [cavityPerturbationCoefficients, tensorLeafCoefficients, cylinderField_feature]
  apply Finset.measurable_sum
  intro i _
  exact (((measurable_cavityRotation_spinTensor I _ _ x.1 i.2).comp measurable_fst).const_mul _).mul
    ((measurable_pi_apply (treeFeatureTag depth x.2 i)).comp measurable_snd)

lemma measurable_cavityRotationHamiltonian {N m depth : ℕ}
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) :
    Measurable (fun p : (Orthogonal N × (ℕ → ℝ)) × (Spin N × LabeledLeaf depth) =>
      cavityRotationHamiltonian (matrixRotation p.1.1⁻¹) eig I u p.1.2 p.2) := by
  apply measurable_from_prod_countable_left
  intro x
  have hr : Measurable (fun V : Orthogonal N =>
      rotatedEnergy eig (matrixRotation V⁻¹) x.1) := by
    unfold rotatedEnergy
    exact (Finset.measurable_sum _ fun i _ =>
      ((measurable_cavityRotation_eval (spinVector x.1) i).pow_const 2).const_mul (eig i)).const_mul _
  exact (hr.comp measurable_fst).add (measurable_cavityRotation_perturbation I u x)

end InvariantIsing

end

end OAI
