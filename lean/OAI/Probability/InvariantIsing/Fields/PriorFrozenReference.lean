import OAI.Probability.InvariantIsing.Fields.PriorTensorReference

namespace OAI

/-! Freezing one actual Gaussian perturbation coordinate with a fixed prior. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal
namespace InvariantIsing

abbrev PriorFrozenData (N j : ℕ) := SpecialOrthogonal N × OtherNamespaces (j+1)

def priorFrozenLaw {N : ℕ} (μ : Measure (SpecialOrthogonal N)) (j : ℕ) :
    Measure (PriorFrozenData N j) := μ.prod (otherNamespacesLaw (j+1))

instance priorFrozenLaw_probability {N : ℕ} (μ : Measure (SpecialOrthogonal N))
    [IsProbabilityMeasure μ] (j : ℕ) : IsProbabilityMeasure (priorFrozenLaw μ j) := by
  unfold priorFrozenLaw
  infer_instance

def priorFrozenInsertion {N : ℕ} (j : ℕ) (p : PriorFrozenData N j × (ℕ → ℝ)) :
    SpecialOrthogonal N × (ℕ → ℝ) :=
  (p.1.1,gaussianNamespaceJoin (j+1) (p.2,p.1.2))

lemma priorFrozenInsertion_preserving {N : ℕ} (μ : Measure (SpecialOrthogonal N))
    [IsProbabilityMeasure μ] (j : ℕ) :
    MeasurePreserving (priorFrozenInsertion j) ((priorFrozenLaw μ j).prod gaussianCoordinates)
      (μ.prod gaussianCoordinates) := namespaceInsertion_preserving μ (j+1)

def priorFrozenBaseEnergy {N m k n : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (r : Fin k → ℕ) (h : ℕ → ℝ) (j : Fin k)
    (ω : PriorFrozenData N j) (x : Spin N × LabeledLeaf n) : ℝ :=
  priorNamespacedHamiltonian eig c I degree (Function.update amplitude j 0)
    (fun i => tensorPathProfile I degree n r h i)
    (ω.1,gaussianNamespaceJoin (j+1) (0,ω.2)) x

def priorFrozenReference {N m k n : ℕ} (ν : Measure (Spin N × LabeledLeaf n))
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (j : Fin k)
    (ω : PriorFrozenData N j) : Measure (Spin N × LabeledLeaf n) :=
  gibbsProbability ν (priorFrozenBaseEnergy eig c I degree amplitude r h j ω)

instance priorFrozenReference_probability {N m k n : ℕ}
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (j : Fin k)
    (ω : PriorFrozenData N j) :
    IsProbabilityMeasure (priorFrozenReference ν eig c I degree amplitude r h j ω) :=
  gibbsProbability_probability _ _

lemma measurable_priorFrozenReference {N m k n : ℕ}
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ) (j : Fin k) :
    Measurable (priorFrozenReference ν eig c I degree amplitude r h j) := by
  have hm : Measurable (fun ω : PriorFrozenData N j =>
      (ω.1,gaussianNamespaceJoin (j+1) (0,ω.2))) :=
    measurable_fst.prodMk ((measurable_gaussianNamespaceJoin (j+1)).comp
      (measurable_const.prodMk measurable_snd))
  exact (measurable_priorNamespacedReference ν eig c I degree (Function.update amplitude j 0)
    (fun i => tensorPathProfile I degree n r h i)).comp hm

lemma priorFrozenHamiltonian_insert {N m k n : ℕ}
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0≤h 0) (j : Fin k)
    (ω : PriorFrozenData N j) (z : ℕ → ℝ) (x : Spin N × LabeledLeaf n) :
    priorNamespacedHamiltonian eig c I degree amplitude
      (fun i => tensorPathProfile I degree n r h i) (priorFrozenInsertion j (ω,z)) x =
    priorFrozenBaseEnergy eig c I degree amplitude r h j ω x + amplitude j *
      cylinderField (jointSpectralMonomialCoefficients (specialRotation ω.1) I (degree j) n (r j) x) z := by
  unfold priorNamespacedHamiltonian priorFrozenBaseEnergy priorFrozenInsertion
  rw [tensorNamespacedField_insert (specialRotation ω.1) I degree amplitude n r h hh h0 j x z ω.2]
  exact (add_assoc _ _ _).symm

theorem priorFrozenBase_exp_integrable_ae {N m k n : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (ν : Measure (Spin N × LabeledLeaf n)) [IsProbabilityMeasure ν]
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0≤h 0) (j : Fin k) :
    ∀ᵐ ω ∂priorFrozenLaw μ j,
      Integrable (fun x => Real.exp (priorFrozenBaseEnergy eig c I degree amplitude r h j ω x)) ν := by
  have he := (priorFrozenInsertion_preserving μ j).quasiMeasurePreserving.ae
    (priorNamespaced_exp_integrable_ae μ ν eig c I degree (Function.update amplitude j 0) r h hh h0)
  have he' : ∀ᵐ p : PriorFrozenData N j × (ℕ → ℝ)
      ∂(priorFrozenLaw μ j).prod gaussianCoordinates,
      Integrable (fun x => Real.exp (priorFrozenBaseEnergy eig c I degree amplitude r h j p.1 x)) ν := by
    filter_upwards [he] with p hp
    convert hp using 1
    funext x
    congr 1
    unfold priorFrozenBaseEnergy priorNamespacedHamiltonian priorFrozenInsertion
    rw [tensorNamespacedField_frozen (specialRotation p.1.1) I degree amplitude n r h hh h0 j x p.2 p.1.2]
  filter_upwards [Measure.ae_ae_of_ae_prod he'] with ω hω
  obtain ⟨z,hz⟩ := hω.exists
  exact hz

end InvariantIsing

end

end OAI
