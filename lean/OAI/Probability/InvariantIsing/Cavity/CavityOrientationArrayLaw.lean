import OAI.Probability.InvariantIsing.Cavity.CavityOrientationProbability
import OAI.Probability.InvariantIsing.Cavity.CavityReplicaDisorderTransport
import OAI.Probability.InvariantIsing.Arrays.TensorArrayLaw

namespace OAI

/-! The concrete base-rotation array is exactly the namespaced tensor
array after orienting its inverse eigenbasis. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

def cavityOrientedBaseLaw {N : ℕ} (hN : 0 < N) (μ : Measure (Orthogonal N)) :
    Measure (SpecialOrthogonal N) :=
  μ.map (fun V => cavityOrientationLift hN V⁻¹)

lemma cavityOrientedBaseLaw_preserving {N : ℕ} (hN : 0 < N)
    (μ : Measure (Orthogonal N)) :
    MeasurePreserving (fun V => cavityOrientationLift hN V⁻¹) μ (cavityOrientedBaseLaw hN μ) :=
  ⟨(measurable_cavityOrientationLift hN).comp measurable_inv, rfl⟩

instance cavityOrientedBaseLaw_probability {N : ℕ} (hN : 0 < N)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (cavityOrientedBaseLaw hN μ) :=
  (Measure.isProbabilityMeasure_map_iff
    ((measurable_cavityOrientationLift hN).comp measurable_inv).aemeasurable).mpr inferInstance

lemma measurable_cavityBaseSOArray {N m depth : ℕ} (I : Fin m → Finset (Fin N)) :
    Measurable (fun p : (SpecialOrthogonal N × LabeledTree depth) ×
      (ℕ → Spin N × LabeledLeaf depth) => fun ij : ℕ × ℕ =>
      spectralJointEntry (specialRotation p.1.1) I depth (p.2 ij.1) (p.2 ij.2)) := by
  exact measurable_spectralReplicaArray (Ω := SpecialOrthogonal N × LabeledTree depth)
    (N := N) (m := m) (fun p => p.1) measurable_fst I depth

theorem cavity_orientation_array_law {N m depth : ℕ} (hN : 0 < N)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ]
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) (b : ℕ → ℝ) :
    cavityRotationArrayLaw μ (labeledCascadeLaw depth b : Measure (LabeledTree depth)) eig I u =
      tensorNamespacedArrayLaw (cavityOrientedBaseLaw hN μ) eig (fun _ => 0) I
        (fun j : Fin N => enumeratedSpectralDegree m j)
        (tensorPerturbationAmplitude N (fun j => u j)) depth b
        (fun j : Fin N => enumeratedTreeDegree m j) (fun _ => 0) := by
  let Ω := Orthogonal N × LabeledTree depth
  let Ξ := SpecialOrthogonal N × LabeledTree depth
  let X := Spin N × LabeledLeaf depth
  let φ : Ω → Ξ := fun p => (cavityOrientationLift hN p.1⁻¹,p.2)
  let ρ : Measure (LabeledTree depth) := labeledCascadeLaw depth b
  let P : Measure Ω := μ.prod ρ
  let Q : Measure Ξ := (cavityOrientedBaseLaw hN μ).prod ρ
  have hφ : MeasurePreserving φ P Q :=
    (cavityOrientedBaseLaw_preserving hN μ).prod (MeasurePreserving.id ρ)
  let η : Ξ × (ℕ → ℝ) → Measure X := tensorNamespacedReference eig (fun _ => 0) I
    (fun j : Fin N => enumeratedSpectralDegree m j)
    (tensorPerturbationAmplitude N (fun j => u j)) depth
    (fun j : Fin N => enumeratedTreeDegree m j) (fun _ => 0)
  have hη : Measurable η := measurable_tensorNamespacedReference (N := N) (m := m) (k := N)
    eig (fun _ => 0) I (fun j : Fin N => enumeratedSpectralDegree m j)
    (tensorPerturbationAmplitude N (fun j => u j)) depth
    (fun j : Fin N => enumeratedTreeDegree m j) (fun _ => 0)
  let ν : Ω × (ℕ → ℝ) → Measure X := cavityRotationProbability eig I u
  have hν : Measurable ν := measurable_cavityRotationProbability (N := N) (m := m) (depth := depth) eig I u
  let (p : Ω × (ℕ → ℝ)) : IsProbabilityMeasure (ν p) :=
    cavityRotationProbability_probability eig I u p
  let (p : Ξ × (ℕ → ℝ)) : IsProbabilityMeasure (η p) :=
    tensorNamespacedReference_probability eig (fun _ => 0) I
      (fun j : Fin N => enumeratedSpectralDegree m j)
      (tensorPerturbationAmplitude N (fun j => u j)) depth
      (fun j : Fin N => enumeratedTreeDegree m j) (fun _ => 0) p
  let (p : Ω × (ℕ → ℝ)) : IsProbabilityMeasure (η (φ p.1,p.2)) := by
    infer_instance
  let A : Ξ → (ℕ → X) → SpectralArray (m+1) := fun p σ ij =>
    spectralJointEntry (specialRotation p.1) I depth (σ ij.1) (σ ij.2)
  have hA : Measurable (Function.uncurry A) := measurable_cavityBaseSOArray I
  let φS : Ω × (ℕ → X) → Ξ × (ℕ → X) := fun p => (φ p.1,p.2)
  have hφS : Measurable φS := hφ.measurable.prodMap measurable_id
  have hAφ : Measurable (Function.uncurry (fun ω => A (φ ω))) := by
    have hh := hA.comp hφS
    exact hh
  let φZ : Ω × (ℕ → ℝ) → Ξ × (ℕ → ℝ) := fun p => (φ p.1,p.2)
  have hφZ : Measurable φZ := hφ.measurable.prodMap measurable_id
  have hηφ : Measurable (fun p : Ω × (ℕ → ℝ) => η (φ p.1,p.2)) := hη.comp hφZ
  have hc := cavity_observed_replica_law_congr (Ω := Ω) (Z := ℕ → ℝ) (X := X)
    (Y := SpectralArray (m+1)) P gaussianCoordinates ν
    (fun p => η (φ p.1,p.2)) hν
    hηφ
    (fun ω => cavity_orientation_tensor_probability_law hN ω.1 ω.2 eig I u)
    (fun ω => A (φ ω)) hAφ
  have ht := cavity_observed_replica_law_transport (Ω := Ω) (Ξ := Ξ) (Z := ℕ → ℝ)
    (X := X) (Y := SpectralArray (m+1)) P Q gaussianCoordinates φ hφ η hη A hA
  have ho : (fun p : (Ω × (ℕ → ℝ)) × (ℕ → X) => A (φ p.1.1) p.2) =
      cavitySampledEntryArray (cavityRotationEntry I) := by
    funext p ij
    exact cavityOrientationLift_jointEntry hN p.1.1.1⁻¹ I (p.2 ij.1) (p.2 ij.2)
  apply Subtype.ext
  change (disorderReplicaLaw (P.prod gaussianCoordinates) ν hν).map
    (cavitySampledEntryArray (cavityRotationEntry I)) =
      (disorderReplicaLaw (Q.prod gaussianCoordinates) η hη).map (fun p => A p.1.1 p.2)
  rw [ho] at hc ht
  exact hc.trans ht

end InvariantIsing

end

end OAI
