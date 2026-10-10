import OAI.Probability.InvariantIsing.Magnetic.RestrictedPriorGaussianLaw
import OAI.Probability.InvariantIsing.Cavity.CavityOrientationArrayLaw
import OAI.Probability.InvariantIsing.Magnetic.RestrictedRotationArray
import OAI.Probability.InvariantIsing.Fields.PriorArrayLaw
import OAI.Probability.InvariantIsing.Cavity.CavityBaseAmplitude
import OAI.Probability.InvariantIsing.Fields.PriorLimitingGG

namespace OAI

/-! Exact physical constrained array law with the trivial auxiliary tree. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing

def restrictedZeroTreePrior {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty) :
    Measure (Spin N × LabeledLeaf 0) :=
  labeledSpinReference 0 (restrictedSpinPrior S hS : Measure (Spin N)) PUnit.unit

instance restrictedZeroTreePrior_probability {N : ℕ} (S : Finset (Spin N)) (hS : S.Nonempty) :
    IsProbabilityMeasure (restrictedZeroTreePrior S hS) := by
  unfold restrictedZeroTreePrior
  exact labeledSpinReference_probability 0 (restrictedSpinPrior S hS : Measure (Spin N)) PUnit.unit

theorem restricted_zero_tree_array_law {N m : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ]
    (ρ : Measure (LabeledTree 0)) [IsProbabilityMeasure ρ]
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) :
    restrictedRotationArrayLaw S hS μ ρ eig I u =
      priorNamespacedArrayLaw (cavityOrientedBaseLaw hN μ) (restrictedZeroTreePrior S hS)
        eig (fun _ => 0) I (fun j : Fin N => enumeratedSpectralDegree m j)
        (tensorPerturbationAmplitude N (fun j => u j))
        (fun j : Fin N => enumeratedTreeDegree m j) (fun _ => 0) := by
  let Ω := Orthogonal N × LabeledTree 0
  let Ξ := SpecialOrthogonal N
  let X := Spin N × LabeledLeaf 0
  let φ : Ω → Ξ := fun p => cavityOrientationLift hN p.1⁻¹
  let P : Measure Ω := μ.prod ρ
  let Q : Measure Ξ := cavityOrientedBaseLaw hN μ
  have hφ : MeasurePreserving φ P Q :=
    (cavityOrientedBaseLaw_preserving hN μ).comp (measurePreserving_fst (μ := μ) (ν := ρ))
  let η : Ξ × (ℕ → ℝ) → Measure X := priorNamespacedReference (restrictedZeroTreePrior S hS)
    eig (fun _ => 0) I (fun j : Fin N => enumeratedSpectralDegree m j)
    (tensorPerturbationAmplitude N (fun j => u j))
    (fun i => tensorPathProfile I (fun j : Fin N => enumeratedSpectralDegree m j) 0
      (fun j : Fin N => enumeratedTreeDegree m j) (fun _ => 0) i)
  have hη : Measurable η := measurable_priorNamespacedReference (restrictedZeroTreePrior S hS)
    eig (fun _ => 0) I (fun j : Fin N => enumeratedSpectralDegree m j)
    (tensorPerturbationAmplitude N (fun j => u j))
    (fun i => tensorPathProfile I (fun j : Fin N => enumeratedSpectralDegree m j) 0
      (fun j : Fin N => enumeratedTreeDegree m j) (fun _ => 0) i)
  let ν : Ω × (ℕ → ℝ) → Measure X := restrictedRotationProbability S hS eig I u
  have hν : Measurable ν := measurable_restrictedRotationProbability S hS eig I u
  let (p : Ω × (ℕ → ℝ)) : IsProbabilityMeasure (ν p) :=
    restrictedRotationProbability_probability S hS eig I u p
  let (p : Ξ × (ℕ → ℝ)) : IsProbabilityMeasure (η p) :=
    priorNamespacedReference_probability (restrictedZeroTreePrior S hS) eig (fun _ => 0) I
      (fun j : Fin N => enumeratedSpectralDegree m j) (tensorPerturbationAmplitude N (fun j => u j))
      (fun i => tensorPathProfile I (fun j : Fin N => enumeratedSpectralDegree m j) 0
        (fun j : Fin N => enumeratedTreeDegree m j) (fun _ => 0) i) p
  let (p : Ω × (ℕ → ℝ)) : IsProbabilityMeasure (η (φ p.1,p.2)) := by infer_instance
  let A : Ξ → (ℕ → X) → SpectralArray (m+1) := fun U σ ij =>
    spectralJointEntry (specialRotation U) I 0 (σ ij.1) (σ ij.2)
  have hA : Measurable (Function.uncurry A) :=
    measurable_spectralReplicaArray (Ω := Ξ) id measurable_id I 0
  let φS : Ω × (ℕ → X) → Ξ × (ℕ → X) := fun p => (φ p.1,p.2)
  have hφS : Measurable φS := hφ.measurable.prodMap measurable_id
  have hAφ : Measurable (Function.uncurry (fun ω => A (φ ω))) := by
    have hh := hA.comp hφS
    exact hh
  let φZ : Ω × (ℕ → ℝ) → Ξ × (ℕ → ℝ) := fun p => (φ p.1,p.2)
  have hφZ : Measurable φZ := hφ.measurable.prodMap measurable_id
  have hηφ : Measurable (fun p : Ω × (ℕ → ℝ) => η (φ p.1,p.2)) := hη.comp hφZ
  have he (ω : Ω) : gaussianCoordinates.map (fun z => ν (ω,z)) =
      gaussianCoordinates.map (fun z => η (φ ω,z)) := by
    have hT : ω.2 = (PUnit.unit : LabeledTree 0) := Subsingleton.elim _ _
    simpa only [ν,η,φ,restrictedZeroTreePrior,hT] using
      restricted_orientation_prior_probability_law hN S hS ω.1 ω.2 eig I u
  have hc := cavity_observed_replica_law_congr P gaussianCoordinates ν
    (fun p => η (φ p.1,p.2)) hν hηφ he (fun ω => A (φ ω)) hAφ
  have ht := cavity_observed_replica_law_transport P Q gaussianCoordinates φ hφ η hη A hA
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

lemma restricted_zero_tree_perturbed_array_law {N m : ℕ} (hN : 0<N)
    (S : Finset (Spin N)) (hS : S.Nonempty)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ]
    (ρ : Measure (LabeledTree 0)) [IsProbabilityMeasure ρ]
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (u : Fin N → ℝ) (v : Fin m → ℝ) (t : ℝ) :
    restrictedRotationArrayLaw S hS μ ρ (diagonalPerturbedEigenvalues eig I v t)
      I (cavityBaseAmplitude u) =
      priorPerturbedArrayLaw (cavityOrientedBaseLaw hN μ) (restrictedZeroTreePrior S hS)
        eig (fun _ => 0) I u v t (fun _ => 0) := by
  unfold priorPerturbedArrayLaw
  simpa only [cavityBaseAmplitude_restrict] using
    restricted_zero_tree_array_law hN S hS μ ρ (diagonalPerturbedEigenvalues eig I v t)
      I (cavityBaseAmplitude u)

end InvariantIsing

end

end OAI
