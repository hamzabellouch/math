import OAI.Probability.InvariantIsing.Cavity.CavityScalarFieldLaw
import OAI.Probability.InvariantIsing.Cavity.CavityMarkDepthLaw

namespace OAI

/-! Projection of the retained Gaussian forest to the independent cavity fields. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix BigOperators NNReal

namespace InvariantIsing

def cavityProjectField {d k : ℕ} (L : Matrix (Fin d) (Fin k) ℝ)
    (z : EuclideanSpace ℝ (Fin d)) : Fin k → ℝ :=
  WithLp.ofLp (L.transpose.toEuclideanLin.toContinuousLinearMap z)

lemma measurable_cavityProjectField {d k : ℕ} (L : Matrix (Fin d) (Fin k) ℝ) :
    Measurable (cavityProjectField L) := by
  unfold cavityProjectField
  fun_prop

lemma cavityProjectField_add {d k : ℕ} (L : Matrix (Fin d) (Fin k) ℝ)
    (z w : EuclideanSpace ℝ (Fin d)) :
    cavityProjectField L (z + w) = cavityProjectField L z + cavityProjectField L w := by
  ext i
  simp [cavityProjectField, map_add]

lemma cavityProjectField_sum {d k : ℕ} {ι : Type*} (L : Matrix (Fin d) (Fin k) ℝ)
    (s : Finset ι) (z : ι → EuclideanSpace ℝ (Fin d)) :
    cavityProjectField L (∑ i ∈ s, z i) = ∑ i ∈ s, cavityProjectField L (z i) := by
  ext j
  simp [cavityProjectField, map_sum]

theorem cavity_projected_forest_law {d k : ℕ} (n : ℕ)
    (S : ℕ → Matrix (Fin d) (Fin d) ℝ) (hS : ∀ i, (S i).PosSemidef)
    (L : Matrix (Fin d) (Fin k) ℝ) (v : ℕ → ℝ≥0)
    (hcov : ∀ i < n, L.transpose * S i * L = (v i : ℝ) • 1) :
    (Measure.infinitePi (fun a : ForestVertex n =>
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (S (forestVertexDepth n a)))).map
        (fun g a => cavityProjectField L (g a)) =
      Measure.infinitePi (fun a : ForestVertex n =>
        (vectorGaussianLaw k (v (forestVertexDepth n a)) : Measure (Fin k → ℝ))) := by
  rw [Measure.infinitePi_map_pi _ (fun _ => measurable_cavityProjectField L)]
  congr 1
  funext a
  exact (cavity_scalar_projected_field_law (S (forestVertexDepth n a))
    (hS _) L (v _) (hcov _ (cavityForestVertexDepth_lt n a))).map_eq

theorem cavity_projected_labeled_forest_law {d k : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (S : ℕ → Matrix (Fin d) (Fin d) ℝ) (hS : ∀ i, (S i).PosSemidef)
    (L : Matrix (Fin d) (Fin k) ℝ) (v : ℕ → ℝ≥0)
    (hcov : ∀ i < n, L.transpose * S i * L = (v i : ℝ) • 1) :
    ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod
      (Measure.infinitePi (fun a : ForestVertex n =>
        multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (S (forestVertexDepth n a))))).map
          (fun p => (p.1, fun a => cavityProjectField L (p.2 a))) =
      (labeledCascadeLaw n b : Measure (LabeledTree n)).prod
        (Measure.infinitePi (fun a : ForestVertex n =>
          (vectorGaussianLaw k (v (forestVertexDepth n a)) : Measure (Fin k → ℝ)))) := by
  have hm : Measurable (fun g : ForestVertex n → EuclideanSpace ℝ (Fin d) =>
      fun a => cavityProjectField L (g a)) :=
    Measurable.of_eval fun a =>
      (measurable_cavityProjectField L).comp (measurable_pi_apply a)
  have hp := Measure.map_prod_map (labeledCascadeLaw n b : Measure (LabeledTree n))
    (Measure.infinitePi (fun a : ForestVertex n =>
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (S (forestVertexDepth n a))))
    measurable_id hm
  rw [Measure.map_id, cavity_projected_forest_law n S hS L v hcov] at hp
  exact hp.symm

theorem cavityProjectField_labeled_sum {d k : ℕ} (n : ℕ)
    (L : Matrix (Fin d) (Fin k) ℝ) (T : LabeledTree n)
    (g : ForestVertex n → EuclideanSpace ℝ (Fin d)) (α : LabeledLeaf n)
    (z : EuclideanSpace ℝ (Fin d)) :
    cavityProjectField L (cavityLeafSum n z
      (labeledNoiseLeaf _ n (T, markForestOfCoords _ n g) α)) =
      labeledEnergy n (markForestOfCoords _ n (fun a => cavityProjectField L (g a))) α
        (cavityProjectField L z) := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    simp only [cavityLeafSum, labeledNoiseLeaf, markForestOfCoords, labeledEnergy]
    rw [ih, cavityProjectField_add]

end InvariantIsing

end

end OAI
