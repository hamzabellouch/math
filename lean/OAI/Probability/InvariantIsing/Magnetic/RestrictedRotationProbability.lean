import OAI.Probability.InvariantIsing.Cavity.CavityRotationProbability
import OAI.Probability.InvariantIsing.Magnetic.RestrictedSpinPrior

namespace OAI

/-! The actual constrained spin/leaf Gibbs probability, with all Haar,
Gaussian and finite-tree disorder retained. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

def restrictedRotationProbability {N m depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (p : (Orthogonal N × LabeledTree depth) × (ℕ → ℝ)) :
    Measure (Spin N × LabeledLeaf depth) :=
  gibbsProbability (labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) p.1.2)
    (cavityRotationHamiltonian (matrixRotation p.1.1⁻¹) eig I u p.2)

instance restrictedRotationProbability_probability {N m depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (p : (Orthogonal N × LabeledTree depth) × (ℕ → ℝ)) :
    IsProbabilityMeasure (restrictedRotationProbability S hS eig I u p) :=
  gibbsProbability_probability _ _

lemma measurable_restrictedRotationProbability {N m depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) :
    Measurable (restrictedRotationProbability (depth := depth) S hS eig I u) := by
  let Ω := (Orthogonal N × LabeledTree depth) × (ℕ → ℝ)
  let X := Spin N × LabeledLeaf depth
  let ν : Ω → Measure X := fun p =>
    labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) p.1.2
  let H : Ω × X → ℝ := fun p =>
    cavityRotationHamiltonian (matrixRotation p.1.1.1⁻¹) eig I u p.1.2 p.2
  let (p : Ω) : IsProbabilityMeasure (ν p) := by
    change IsProbabilityMeasure (labeledSpinReference depth
      (restrictedSpinPrior S hS : Measure (Spin N)) p.1.2)
    infer_instance
  have hν : Measurable ν :=
    (measurable_labeledSpinReference_general depth
      (restrictedSpinPrior S hS : Measure (Spin N))).comp measurable_fst.snd
  have hH : Measurable H := measurable_cavityRotationProbabilityHamiltonian eig I u
  exact measurable_gibbsProbability (ν := ν) (H := H) hν hH

lemma restricted_rotation_exp_integrable_ae {N m depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (V : Rotation N) (T : LabeledTree depth)
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2) :
    ∀ᵐ z ∂gaussianCoordinates, Integrable
      (fun x => Real.exp (cavityRotationHamiltonian V eig I u z x))
      (labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T) := by
  let ν := labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T
  exact cylinder_partition_exp_integrable_ae ν (fun x => rotatedEnergy eig V x.1)
    (cavity_bounded_base_exp_integrable ν _ (fun x =>
      Finset.single_le_sum (f := fun σ : Spin N => |rotatedEnergy eig V σ|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ x.1)))
    (cavityPerturbationCoefficients V I u depth)
    (cavityPerturbationCoefficients_sq_le V I u hu)

lemma restrictedRotationProbability_eq_tilted_ae {N m depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty)
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2) (V : Orthogonal N) (T : LabeledTree depth) :
    ∀ᵐ z ∂gaussianCoordinates, restrictedRotationProbability S hS eig I u ((V,T),z) =
      (labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T).tilted
        (cavityRotationHamiltonian (matrixRotation V⁻¹) eig I u z) := by
  filter_upwards [restricted_rotation_exp_integrable_ae S hS (matrixRotation V⁻¹) T eig I u hu]
    with z hz
  exact gibbsProbability_eq_tilted _ _ hz


end InvariantIsing

end

end OAI
