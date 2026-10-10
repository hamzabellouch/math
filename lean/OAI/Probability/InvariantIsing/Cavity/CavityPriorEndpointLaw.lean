import OAI.Probability.InvariantIsing.Cavity.CavityLabeledModel
import OAI.Probability.InvariantIsing.Cavity.CavityOneReplicaGaussian

namespace OAI

/-! A fixed labeled path, its common Gaussian root, and its independent
ordinary residual have the full unweighted endpoint covariance. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma cavity_forest_leaf_sum_law {d : ℕ} (n : ℕ)
    (S : ℕ → Matrix (Fin d) (Fin d) ℝ) (hS : ∀ i, (S i).PosSemidef)
    (α : LabeledLeaf n) :
    (Measure.infinitePi (fun v : ForestVertex n =>
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (S (forestVertexDepth n v)))).map
      (fun g => ∑ i : Fin n, g (edgeAt n α i)) =
    multivariateGaussian 0 (∑ i : Fin n, S i) := by
  have hsel := cavity_selected_path_law n (cavityGaussianMarks S) α
  have hm : Measurable (fun z : Fin n → EuclideanSpace ℝ (Fin d) => ∑ i, z i) := by fun_prop
  have he := congrArg (fun μ : Measure (Fin n → EuclideanSpace ℝ (Fin d)) =>
    μ.map (fun z => ∑ i, z i)) hsel
  rw [Measure.map_map hm (by fun_prop)] at he
  exact he.trans (cavity_gaussian_sum_law (fun i : Fin n => S i) (fun i => hS i))

lemma cavity_root_forest_leaf_law {d : ℕ} (n : ℕ)
    (S₀ : Matrix (Fin d) (Fin d) ℝ) (S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hS₀ : S₀.PosSemidef) (hS : ∀ i, (S i).PosSemidef) (α : LabeledLeaf n) :
    ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
      (Measure.infinitePi (fun v : ForestVertex n =>
        multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (S (forestVertexDepth n v))))).map
      (fun z => z.1 + ∑ i : Fin n, z.2 (edgeAt n α i)) =
    multivariateGaussian 0 (S₀ + ∑ i : Fin n, S i) := by
  let PG := Measure.infinitePi (fun v : ForestVertex n =>
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (S (forestVertexDepth n v)))
  let f := fun g : ForestVertex n → EuclideanSpace ℝ (Fin d) => ∑ i : Fin n, g (edgeAt n α i)
  have hf : Measurable f := by unfold f; fun_prop
  have he := Measure.map_prod_map (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀)
    PG measurable_id hf
  rw [Measure.map_id, cavity_forest_leaf_sum_law n S hS α] at he
  change ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod PG).map
    ((fun p => p.1 + p.2) ∘ Prod.map id f) = _
  rw [← Measure.map_map (by fun_prop) (measurable_id.prodMap hf), ← he]
  exact cavity_gaussian_add_law S₀ _ hS₀ (Matrix.posSemidef_sum Finset.univ (fun i _ => hS i))

lemma cavity_prior_endpoint_law {d : ℕ} (n : ℕ)
    (S₀ R : Matrix (Fin d) (Fin d) ℝ) (S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hS₀ : S₀.PosSemidef) (hR : R.PosSemidef) (hS : ∀ i, (S i).PosSemidef)
    (α : LabeledLeaf n) :
    (((multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
      (Measure.infinitePi (fun v : ForestVertex n =>
        multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (S (forestVertexDepth n v))))).prod
          (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) R)).map
      (fun z => (z.1.1 + ∑ i : Fin n, z.1.2 (edgeAt n α i)) + z.2) =
    multivariateGaussian 0 ((S₀ + ∑ i : Fin n, S i) + R) := by
  let PS := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
    (Measure.infinitePi (fun v : ForestVertex n =>
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (S (forestVertexDepth n v))))
  let f := fun z : EuclideanSpace ℝ (Fin d) × (ForestVertex n → EuclideanSpace ℝ (Fin d)) =>
    z.1 + ∑ i : Fin n, z.2 (edgeAt n α i)
  have hf : Measurable f := by unfold f; fun_prop
  have he := Measure.map_prod_map PS (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) R)
    hf measurable_id
  rw [Measure.map_id, cavity_root_forest_leaf_law n S₀ S hS₀ hS α] at he
  change (PS.prod (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) R)).map
    ((fun p => p.1 + p.2) ∘ Prod.map f id) = _
  rw [← Measure.map_map (by fun_prop) (hf.prodMap measurable_id), ← he]
  exact cavity_gaussian_add_law _ R (hS₀.add (Matrix.posSemidef_sum Finset.univ (fun i _ => hS i))) hR

end InvariantIsing

end

end OAI
