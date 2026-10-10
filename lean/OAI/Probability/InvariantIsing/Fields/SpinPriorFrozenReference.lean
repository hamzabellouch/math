import OAI.Probability.InvariantIsing.Fields.SpinPriorExponential

namespace OAI

/-! One independent Gaussian coordinate frozen inside the actual constrained
cascade model. The cascade tree remains part of the external disorder. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal
namespace InvariantIsing

def spinPriorFrozenReference {N m k : ℕ} (π : Measure (Spin N))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amp : Fin k → ℝ) (n : ℕ) (r : Fin k → ℕ) (h : ℕ → ℝ) (j : Fin k)
    (ω : TensorFrozenData N n j) : Measure (Spin N × LabeledLeaf n) :=
  gibbsProbability (labeledSpinReference n π ω.1.2)
    (tensorFrozenBaseEnergy eig c I degree amp n r h j ω)

instance spinPriorFrozenReference_probability {N m k : ℕ} (π : Measure (Spin N))
    [IsProbabilityMeasure π] (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ) (n : ℕ) (r : Fin k → ℕ)
    (h : ℕ → ℝ) (j : Fin k) (ω : TensorFrozenData N n j) :
    IsProbabilityMeasure (spinPriorFrozenReference π eig c I degree amp n r h j ω) :=
  gibbsProbability_probability _ _

lemma measurable_spinPriorFrozenReference {N m k : ℕ} (π : Measure (Spin N))
    [IsProbabilityMeasure π] (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ) (n : ℕ) (r : Fin k → ℕ)
    (h : ℕ → ℝ) (j : Fin k) :
    Measurable (spinPriorFrozenReference π eig c I degree amp n r h j) := by
  have : ∀ ω : TensorFrozenData N n j, IsProbabilityMeasure
      ((labeledSpinReference n π ∘ fun ω : TensorFrozenData N n j => ω.1.2) ω) := fun ω => by
        change IsProbabilityMeasure (labeledSpinReference n π ω.1.2)
        infer_instance
  exact measurable_gibbsProbability
    (H := Function.uncurry (tensorFrozenBaseEnergy eig c I degree amp n r h j))
    ((measurable_labeledSpinReference_general n π).comp measurable_fst.snd)
    (measurable_tensorFrozenBaseEnergy eig c I degree amp n r h j)

theorem spinPriorFrozenBase_exp_integrable_ae {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0 ≤ h 0) (j : Fin k) :
    ∀ᵐ ω ∂tensorFrozenLaw μ n b j,
      Integrable (fun x => Real.exp (tensorFrozenBaseEnergy eig c I degree amp n r h j ω x))
        (labeledSpinReference n π ω.1.2) := by
  have he := (tensorFrozenInsertion_measurePreserving μ n b j).quasiMeasurePreserving.ae
    (spinPriorNamespaced_exp_integrable_ae μ π eig c I degree (Function.update amp j 0) n b r h hh h0)
  have he' : ∀ᵐ p : TensorFrozenData N n j × (ℕ → ℝ)
      ∂(tensorFrozenLaw μ n b j).prod gaussianCoordinates,
      Integrable (fun x => Real.exp (tensorFrozenBaseEnergy eig c I degree amp n r h j p.1 x))
        (labeledSpinReference n π p.1.1.2) := by
    filter_upwards [he] with p hp
    convert hp using 1
    funext x
    congr 1
    unfold tensorFrozenBaseEnergy
    rw [tensorNamespacedField_frozen (specialRotation p.1.1.1) I degree amp n r h hh h0 j x p.2 p.1.2]
  filter_upwards [Measure.ae_ae_of_ae_prod he'] with ω hω
  obtain ⟨z,hz⟩ := hω.exists
  exact hz

end InvariantIsing

end

end OAI
