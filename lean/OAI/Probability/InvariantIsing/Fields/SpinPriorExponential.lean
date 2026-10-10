import OAI.Probability.InvariantIsing.Fields.SpinPriorCascadePressure

namespace OAI

/-! Exponential integrability of the actual cascade-enriched Hamiltonian
for a normalized deterministic spin constraint. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Topology
namespace InvariantIsing

theorem spinPriorNamespaced_exp_integrable_ae {N m k : ℕ}
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (treeDegree : Fin k → ℕ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) :
    ∀ᵐ p : (SpecialOrthogonal N × LabeledTree n) × (ℕ → ℝ)
      ∂(μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates,
      Integrable (fun x : Spin N × LabeledLeaf n => Real.exp
        (rotatedEnergy eig (specialRotation p.1.1) x.1 + fieldEnergy c x.1 +
          cylinderField (tensorNamespacedCoefficients (specialRotation p.1.1) I degree amplitude n
            (fun i => tensorPathProfile I degree n treeDegree h i) x) p.2))
        (labeledSpinReference n π p.1.2) := by
  let Ω := SpecialOrthogonal N × LabeledTree n
  let ν := fun ω : Ω => labeledSpinReference n π ω.2
  let H := fun (ω : Ω) (x : Spin N × LabeledLeaf n) =>
    rotatedEnergy eig (specialRotation ω.1) x.1 + fieldEnergy c x.1
  let A := fun (ω : Ω) => tensorNamespacedCoefficients (specialRotation ω.1) I degree amplitude n
    (fun i => tensorPathProfile I degree n treeDegree h i)
  have : ∀ ω, IsProbabilityMeasure (ν ω) := fun ω => by
    change IsProbabilityMeasure (labeledSpinReference n π ω.2)
    infer_instance
  have hν : Measurable ν :=
    (measurable_labeledSpinReference_general n π).comp measurable_snd
  have hbase (ω : Ω) : Integrable (fun x => Real.exp (H ω x)) (ν ω) :=
    finite_spin_base_exp_integrable (ν ω)
      (fun σ => rotatedEnergy eig (specialRotation ω.1) σ+fieldEnergy c σ)
  have : ∀ ω, IsProbabilityMeasure ((ν ω).tilted (H ω)) := fun ω => isProbabilityMeasure_tilted (hbase ω)
  have htilt : Measurable (fun ω => (ν ω).tilted (H ω)) :=
    measurable_random_tilted_measure (H := Function.uncurry H) hν (measurable_tensorDeterministicEnergy eig c n)
  have hAm : Measurable (fun p : (Ω × (ℕ → ℝ)) × (Spin N × LabeledLeaf n) =>
      cylinderField (A p.1.1 p.2) p.1.2) := measurable_tensorNamespacedPathFields I degree amplitude n treeDegree h
  have hA (ω : Ω) (x : Spin N × LabeledLeaf n) :
      (A ω x).sum (fun _ c => c ^ 2) ≤ h n * N + ∑ j, amplitude j ^ 2 :=
    tensorNamespacedPath_variance_le (specialRotation ω.1) I degree amplitude n treeDegree h hh h0 x
  have he := randomCoefficient_all_exp_ae
    (P := μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))) htilt A hAm hA
  filter_upwards [he] with p hp
  have hi := hp 1
  rw [integrable_tilted_iff (hbase p.1)] at hi
  simpa only [H, A, ν, one_mul, smul_eq_mul, ← Real.exp_add] using hi


end InvariantIsing

end

end OAI
