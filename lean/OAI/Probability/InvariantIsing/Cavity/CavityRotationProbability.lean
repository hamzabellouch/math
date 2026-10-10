import OAI.Probability.InvariantIsing.Cavity.CavityRotationMeasurability
import OAI.Probability.InvariantIsing.Cavity.CavityRotationCutoffWeight

namespace OAI

/-! The actual measurable base spin/leaf Gibbs probability, with its
rotation, cascade weights and Gaussian disorder all retained. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

def cavityRotationProbability {N m depth : ℕ} (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (p : (Orthogonal N × LabeledTree depth) × (ℕ → ℝ)) :
    Measure (Spin N × LabeledLeaf depth) :=
  gibbsProbability (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) p.1.2)
    (cavityRotationHamiltonian (matrixRotation p.1.1⁻¹) eig I u p.2)

instance cavityRotationProbability_probability {N m depth : ℕ} (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (p : (Orthogonal N × LabeledTree depth) × (ℕ → ℝ)) :
    IsProbabilityMeasure (cavityRotationProbability eig I u p) :=
  gibbsProbability_probability _ _

lemma measurable_cavityRotationProbabilityHamiltonian {N m depth : ℕ}
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) :
    Measurable (fun p : (((Orthogonal N × LabeledTree depth) × (ℕ → ℝ)) ×
      (Spin N × LabeledLeaf depth)) =>
      cavityRotationHamiltonian (matrixRotation p.1.1.1⁻¹) eig I u p.1.2 p.2) := by
  let π : (((Orthogonal N × LabeledTree depth) × (ℕ → ℝ)) ×
      (Spin N × LabeledLeaf depth)) → (Orthogonal N × (ℕ → ℝ)) ×
      (Spin N × LabeledLeaf depth) := fun p => ((p.1.1.1,p.1.2),p.2)
  have hπ : Measurable π :=
    (measurable_fst.fst.fst.prodMk measurable_fst.snd).prodMk measurable_snd
  have hb := measurable_cavityRotationHamiltonian (N := N) (m := m) (depth := depth) eig I u
  have hh := hb.comp hπ
  exact hh

lemma measurable_cavityRotationProbability {N m depth : ℕ} (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) :
    Measurable (cavityRotationProbability (depth := depth) eig I u) := by
  let Ω := (Orthogonal N × LabeledTree depth) × (ℕ → ℝ)
  let X := Spin N × LabeledLeaf depth
  let ν : Ω → Measure X := fun p =>
    labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) p.1.2
  let H : Ω × X → ℝ := fun p =>
    cavityRotationHamiltonian (matrixRotation p.1.1.1⁻¹) eig I u p.1.2 p.2
  let (p : Ω) : IsProbabilityMeasure (ν p) := by
    change IsProbabilityMeasure (labeledSpinReference depth
      (uniformSpinPrior N : Measure (Spin N)) p.1.2)
    infer_instance
  have hν : Measurable ν :=
    (measurable_labeledSpinReference_general depth
      (uniformSpinPrior N : Measure (Spin N))).comp measurable_fst.snd
  have hH : Measurable H := measurable_cavityRotationProbabilityHamiltonian eig I u
  exact measurable_gibbsProbability (ν := ν) (H := H) hν hH

lemma cavityRotationProbability_eq_tilted_ae {N m depth : ℕ}
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N))
    (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2) (V : Orthogonal N) (T : LabeledTree depth) :
    ∀ᵐ z ∂gaussianCoordinates, cavityRotationProbability eig I u ((V,T),z) =
      (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T).tilted
        (cavityRotationHamiltonian (matrixRotation V⁻¹) eig I u z) := by
  filter_upwards [cavity_rotation_exp_integrable_ae (matrixRotation V⁻¹) T eig I u hu]
    with z hz
  exact gibbsProbability_eq_tilted _ _ hz

lemma cavity_rotation_cutoff_probability {N n m depth : ℕ}
    (V : Orthogonal N) (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (W : Spin N × Spin n → ℝ)
    (s : Set ((Spin N × LabeledLeaf depth) × Spin n))
    (F : (Fin 2 → (Spin N × LabeledLeaf depth) × Spin n) → ℝ) :
    (∫ z, cavityCutoffReplicaMean
      ((labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T).prod
        (uniformSpinPrior n))
      (fun x => cavityRotationHamiltonian (matrixRotation V⁻¹) eig I u z x.1 + W (x.1.1,x.2))
      s F ∂gaussianCoordinates) =
    ∫ z, cavityWeightedReplicaMean
      ((cavityRotationProbability eig I u ((V,T),z)).prod (uniformSpinPrior n))
      (s.indicator (fun x => Real.exp (W (x.1.1,x.2)))) F ∂gaussianCoordinates := by
  rw [cavity_rotation_cutoff_weight (matrixRotation V⁻¹) T eig I u hu W s F]
  apply integral_congr_ae
  filter_upwards [cavityRotationProbability_eq_tilted_ae eig I u hu V T] with z hz
  rw [hz]

end InvariantIsing

end

end OAI
