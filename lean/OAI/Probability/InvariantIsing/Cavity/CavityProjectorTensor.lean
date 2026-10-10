import OAI.Probability.InvariantIsing.Cavity.CavityProjectorCoordinates
import OAI.Probability.InvariantIsing.Cavity.CavityRotationMeasurability

namespace OAI

/-! Tensor features built directly from labeled spectral projectors.
They give an eigenbasis-free representation of the actual Gaussian
perturbation, with exactly its original covariance. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Matrix NNReal

namespace InvariantIsing

abbrev CavityProjectorTensorIndex (N m : ℕ) (degree : Fin N → Fin m → ℕ) :=
  SpinTensorIndex (fun _ : Fin m => (Finset.univ : Finset (Fin N))) degree

def cavityProjectorMonomial {N m : ℕ} (Q : Fin m → Matrix (Fin N) (Fin N) ℝ)
    (degree : Fin m → ℕ) (σ : Spin N)
    (v : SpectralTensorIndex (fun _ : Fin m => (Finset.univ : Finset (Fin N))) degree) : ℝ :=
  ∏ a, tensorFeature (degree a) (fun i : (Finset.univ : Finset (Fin N)) =>
    cavityProjectorSpinCoordinate (Q a) σ (i : Fin N)) (v a)

lemma cavityProjectorMonomial_cross {N m : ℕ} (V : Orthogonal N)
    (I : Fin m → Finset (Fin N)) (degree : Fin m → ℕ) (σ τ : Spin N) :
    (∑ w, cavityProjectorMonomial (fun a => cavitySpectralProjector V (I a)) degree σ w *
      cavityProjectorMonomial (fun a => cavitySpectralProjector V (I a)) degree τ w) =
      ∏ a, projectedOverlap (matrixRotation V⁻¹) (I a) σ τ ^ degree a := by
  simp only [cavityProjectorMonomial, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun a (w : Fin (degree a) → (Finset.univ : Finset (Fin N))) =>
    tensorFeature (degree a)
      (fun i : (Finset.univ : Finset (Fin N)) => cavityProjectorSpinCoordinate (cavitySpectralProjector V (I a)) σ (i : Fin N)) w *
    tensorFeature (degree a)
      (fun i : (Finset.univ : Finset (Fin N)) => cavityProjectorSpinCoordinate (cavitySpectralProjector V (I a)) τ (i : Fin N)) w)]
  simp_rw [tensorFeature_cross]
  congr 1
  funext a
  congr 1
  have h := cavity_projector_coordinate_covariance V (I a) σ τ
  exact (Finset.sum_coe_sort Finset.univ _).trans h

def cavityProjectorSpinFeature {N m : ℕ}
    (Q : Fin m → Matrix (Fin N) (Fin N) ℝ)
    (degree : Fin N → Fin m → ℕ) (amp : Fin N → ℝ) (σ : Spin N) :
    CavityProjectorTensorIndex N m degree → ℝ
  | Sum.inl i => spinValue (σ i)
  | Sum.inr w => amp w.1 * cavityProjectorMonomial Q (degree w.1) σ w.2

lemma cavityProjectorSpinFeature_covariance {N m : ℕ} (V : Orthogonal N)
    (I : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ)
    (amp : Fin N → ℝ) (site : ℝ≥0) (mono : Fin N → ℝ≥0) (σ τ : Spin N) :
    (∑ i : CavityProjectorTensorIndex N m degree,
      (tensorVarianceProfile (fun _ => Finset.univ) degree site mono i : ℝ) *
      cavityProjectorSpinFeature (fun a => cavitySpectralProjector V (I a)) degree amp σ i *
      cavityProjectorSpinFeature (fun a => cavitySpectralProjector V (I a)) degree amp τ i) =
    (site:ℝ) * (∑ j, spinValue (σ j)*spinValue (τ j)) +
      ∑ j, (mono j:ℝ)*amp j^2 * ∏ a, projectedOverlap (matrixRotation V⁻¹) (I a) σ τ ^ degree j a := by
  rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  simp only [tensorVarianceProfile, cavityProjectorSpinFeature]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · apply Finset.sum_congr rfl
    intro j _
    calc
      _ = (mono j:ℝ)*amp j^2 * ∑ w,
          cavityProjectorMonomial (fun a => cavitySpectralProjector V (I a)) (degree j) σ w *
          cavityProjectorMonomial (fun a => cavitySpectralProjector V (I a)) (degree j) τ w := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro w _
        ring
      _ = _ := by rw [cavityProjectorMonomial_cross]

def cavityProjectorPerturbation {N m depth : ℕ}
    (Q : Fin m → Matrix (Fin N) (Fin N) ℝ) (u : ℕ → ℝ)
    (x : Spin N × LabeledLeaf depth) : ℕ →₀ ℝ :=
  featureCoefficients (treeFeatureTag depth x.2)
    (fun i : Fin (depth+1) × CavityProjectorTensorIndex N m (fun j => enumeratedSpectralDegree m j) =>
      (NNReal.sqrt (tensorPathProfile (fun _ : Fin m => (Finset.univ : Finset (Fin N)))
        (fun j : Fin N => enumeratedSpectralDegree m j) depth
        (fun j => enumeratedTreeDegree m j) (fun _ => 0) i.1 i.2) : ℝ) *
        cavityProjectorSpinFeature Q (fun j => enumeratedSpectralDegree m j)
          (tensorPerturbationAmplitude N (fun j => u j)) x.1 i.2)

 theorem cavityProjectorPerturbation_cross {N m depth : ℕ} (V : Orthogonal N)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (x y : Spin N × LabeledLeaf depth) :
    cylinderCross (cavityProjectorPerturbation (fun a => cavitySpectralProjector V (I a)) u x)
      (cavityProjectorPerturbation (fun a => cavitySpectralProjector V (I a)) u y) =
    cylinderCross (cavityPerturbationCoefficients (matrixRotation V⁻¹) I u depth x)
      (cavityPerturbationCoefficients (matrixRotation V⁻¹) I u depth y) := by
  classical
  let deg := fun j : Fin N => enumeratedSpectralDegree m j
  let amp := tensorPerturbationAmplitude N (fun j => u j)
  let v := fun i => tensorPathProfile (fun _ : Fin m => (Finset.univ : Finset (Fin N)))
    deg depth (fun j => enumeratedTreeDegree m j) (fun _ => 0) i
  let f := fun σ => cavityProjectorSpinFeature (fun a => cavitySpectralProjector V (I a)) deg amp σ
  rw [cavityProjectorPerturbation, cavityProjectorPerturbation,
    featureCoefficients_diagonal (treeFeatureTag depth x.2) (treeFeatureTag depth y.2)
      (fun i j h => ((treeFeatureTag_cross depth x.2 y.2 i j).mp h).1)]
  simp_rw [treeFeatureTag_cross, true_and]
  rw [Fintype.sum_prod_type, cavityPerturbationCoefficients, cavityPerturbationCoefficients,
    tensorLeafCoefficients_cross]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.1 ≤ labeledCommonDepth depth x.2 y.2
  · simp only [hi, ite_true]
    have hprod (j : CavityProjectorTensorIndex N m deg) :
        ((NNReal.sqrt (v i j) : ℝ) * f x.1 j) * ((NNReal.sqrt (v i j) : ℝ) * f y.1 j) =
        (v i j : ℝ) * f x.1 j * f y.1 j := by
      have hs : (NNReal.sqrt (v i j) : ℝ)^2 = (v i j : ℝ) := by
        exact_mod_cast NNReal.sq_sqrt (v i j)
      calc
        _ = (NNReal.sqrt (v i j) : ℝ)^2 * f x.1 j * f y.1 j := by ring
        _ = _ := by rw [hs]
    change (∑ j : CavityProjectorTensorIndex N m deg,
      ((NNReal.sqrt (v i j) : ℝ) * f x.1 j) * ((NNReal.sqrt (v i j) : ℝ) * f y.1 j)) = _
    simp_rw [hprod]
    change (∑ j, (tensorVarianceProfile (fun _ : Fin m => (Finset.univ : Finset (Fin N))) deg
      (varianceIncrement (fun _ => 0) i) (fun j => varianceIncrement
        (monomialPath depth (enumeratedTreeDegree m j)) i) j : ℝ) *
        cavityProjectorSpinFeature (fun a => cavitySpectralProjector V (I a)) deg amp x.1 j *
        cavityProjectorSpinFeature (fun a => cavitySpectralProjector V (I a)) deg amp y.1 j) = _
    rw [cavityProjectorSpinFeature_covariance]
    dsimp only [tensorPathProfile]
    rw [spinTensorFeature_covariance]
  · simp only [hi, ite_false, Finset.sum_const_zero]

end InvariantIsing

end

end OAI
