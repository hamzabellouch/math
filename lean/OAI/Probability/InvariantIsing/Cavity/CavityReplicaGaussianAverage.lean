import OAI.Probability.InvariantIsing.Cavity.CavityReplicaNodeProjection

namespace OAI

/-! Bounded replica tests may be averaged over the actual Gaussian
root and forest before, or after, sampling the labeled leaves. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix BigOperators

namespace InvariantIsing

def cavityReplicaField {r d : ℕ} (n : ℕ) (T : LabeledTree n)
    (σ : Fin r → LabeledLeaf n)
    (z : (EuclideanSpace ℝ (Fin d) × (ForestVertex n → EuclideanSpace ℝ (Fin d))) ×
      (Fin r → EuclideanSpace ℝ (Fin d))) : EuclideanSpace ℝ (Fin r × Fin d) :=
  WithLp.toLp 2 (fun u =>
    (cavityLeafSum n z.1.1 (labeledNoiseLeaf _ n
      (T, markForestOfCoords _ n z.1.2) (σ u.1)) + z.2 u.1) u.2)

lemma measurable_cavityReplicaField {r d : ℕ} (n : ℕ) (T : LabeledTree n)
    (σ : Fin r → LabeledLeaf n) : Measurable (cavityReplicaField (d := d) n T σ) := by
  let F : (CavityReplicaNode n r → EuclideanSpace ℝ (Fin d)) →
      EuclideanSpace ℝ (Fin r × Fin d) :=
    fun z => cavityGaussianNodeSum (cavityReplicaNodeWeight n σ)
      (fun a : cavityReplicaNodeSupport n σ => z a)
  have hF : Measurable F := by
    unfold F cavityGaussianNodeSum
    fun_prop
  have he : F ∘ cavityReplicaNodeJoin (d := d) n r = cavityReplicaField n T σ := by
    funext z
    exact cavity_replica_node_field n σ T z
  rw [← he]
  exact hF.comp (measurable_cavityReplicaNodeJoin n r)

lemma cavity_replica_gaussian_test {r d : ℕ} (n : ℕ)
    (S₀ R : Matrix (Fin d) (Fin d) ℝ) (S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hS₀ : S₀.PosSemidef) (hR : R.PosSemidef) (hS : ∀ i, (S i).PosSemidef)
    (T : LabeledTree n) (σ : Fin r → LabeledLeaf n)
    (F : EuclideanSpace ℝ (Fin r × Fin d) → ℝ) (hF : Measurable F) :
    (∫ z, F (cavityReplicaField n T σ z)
      ∂(((multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
        (Measure.infinitePi (fun v : ForestVertex n => multivariateGaussian
          (0 : EuclideanSpace ℝ (Fin d)) (S (forestVertexDepth n v))))).prod
          (Measure.pi (fun _ : Fin r => multivariateGaussian
            (0 : EuclideanSpace ℝ (Fin d)) R)))) =
      ∫ y, F y ∂multivariateGaussian 0 (cavityReplicaGaussianCovariance n S₀ R S σ) := by
  rw [← cavity_replica_gaussian_field_law n S₀ R S hS₀ hR hS T σ]
  exact (integral_map (measurable_cavityReplicaField n T σ).aemeasurable
    hF.aestronglyMeasurable).symm

theorem cavity_replica_gaussian_average {r d : ℕ} (n : ℕ)
    (S₀ R : Matrix (Fin d) (Fin d) ℝ) (S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hS₀ : S₀.PosSemidef) (hR : R.PosSemidef) (hS : ∀ i, (S i).PosSemidef)
    (T : LabeledTree n) (ν : Measure (Fin r → LabeledLeaf n)) [IsProbabilityMeasure ν]
    (F : (Fin r → LabeledLeaf n) × EuclideanSpace ℝ (Fin r × Fin d) → ℝ)
    (hF : Measurable F) (C : ℝ) (hbound : ∀ x, ‖F x‖ ≤ C) :
    (∫ z, ∫ σ, F (σ, cavityReplicaField n T σ z) ∂ν
      ∂(((multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
        (Measure.infinitePi (fun v : ForestVertex n => multivariateGaussian
          (0 : EuclideanSpace ℝ (Fin d)) (S (forestVertexDepth n v))))).prod
          (Measure.pi (fun _ : Fin r => multivariateGaussian
            (0 : EuclideanSpace ℝ (Fin d)) R)))) =
      ∫ σ, ∫ y, F (σ, y)
        ∂multivariateGaussian 0 (cavityReplicaGaussianCovariance n S₀ R S σ) ∂ν := by
  let P := ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
    (Measure.infinitePi (fun v : ForestVertex n => multivariateGaussian
      (0 : EuclideanSpace ℝ (Fin d)) (S (forestVertexDepth n v))))).prod
        (Measure.pi (fun _ : Fin r => multivariateGaussian
          (0 : EuclideanSpace ℝ (Fin d)) R))
  have hm : Measurable (fun zσ :
      ((EuclideanSpace ℝ (Fin d) × (ForestVertex n → EuclideanSpace ℝ (Fin d))) ×
        (Fin r → EuclideanSpace ℝ (Fin d))) × (Fin r → LabeledLeaf n) =>
      F (zσ.2, cavityReplicaField n T zσ.2 zσ.1)) := by
    apply measurable_from_prod_countable_left
    intro σ
    exact hF.comp (measurable_const.prodMk (measurable_cavityReplicaField n T σ))
  have hi : Integrable (fun zσ => F (zσ.2, cavityReplicaField n T zσ.2 zσ.1)) (P.prod ν) :=
    (integrable_const C).mono' hm.aestronglyMeasurable (ae_of_all _ fun _ => hbound _)
  rw [integral_integral_swap hi]
  apply integral_congr_ae
  exact ae_of_all _ fun σ => cavity_replica_gaussian_test n S₀ R S hS₀ hR hS T σ
    (fun y => F (σ, y)) (hF.comp (measurable_const.prodMk measurable_id))

end InvariantIsing

end

end OAI
