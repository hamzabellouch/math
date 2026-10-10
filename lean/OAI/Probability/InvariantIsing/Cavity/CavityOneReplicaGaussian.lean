import OAI.Probability.InvariantIsing.Cavity.CavityOneReplicaPath
import OAI.Probability.InvariantIsing.Cavity.CavityGaussianSum

namespace OAI

/-! Gaussian marginal of a single sampled innovation leaf and its residual. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators RealInnerProductSpace

namespace InvariantIsing

theorem cavity_marked_leaf_sum_law {d : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) (S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hS : ∀ i, (S i).PosSemidef) :
    (markedReplicaLaw n b (cavityGaussianMarks S)).map
      (fun σ => cavityLeafSum n 0 (σ 0)) =
      multivariateGaussian 0 (∑ i : Fin n, S i) := by
  have hm : Measurable (fun x : Fin n → EuclideanSpace ℝ (Fin d) => ∑ i, x i) := by
    fun_prop
  have hp : Measurable (fun σ : ℕ → NoiseLeaf (EuclideanSpace ℝ (Fin d)) n =>
      noiseLeafMark n (σ 0)) := by
    apply Measurable.of_eval
    intro i
    exact (measurable_noiseLeafMark n i).comp (measurable_pi_apply 0)
  have he := congrArg (fun P : Measure (Fin n → EuclideanSpace ℝ (Fin d)) =>
      P.map (fun x => ∑ i, x i)) (cavity_marked_one_path_law n b hb (cavityGaussianMarks S))
  rw [Measure.map_map hm hp] at he
  simp only [cavityLeafSum_eq_mark_sum, zero_add]
  exact he.trans (cavity_gaussian_sum_law (fun i : Fin n => S i) (fun i => hS i))

theorem cavity_marked_leaf_residual_law {d : ℕ} (n : ℕ) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) (S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hS : ∀ i, (S i).PosSemidef) (R : Matrix (Fin d) (Fin d) ℝ)
    (hR : R.PosSemidef) :
    ((markedReplicaLaw n b (cavityGaussianMarks S)).prod (multivariateGaussian 0 R)).map
      (fun p => cavityLeafSum n 0 (p.1 0) + p.2) =
      multivariateGaussian 0 ((∑ i : Fin n, S i) + R) := by
  have hl : Measurable (fun σ : ℕ → NoiseLeaf (EuclideanSpace ℝ (Fin d)) n =>
      cavityLeafSum n 0 (σ 0)) :=
    (measurable_cavityLeafSum n 0).comp (measurable_pi_apply 0)
  have he := Measure.map_prod_map (markedReplicaLaw n b (cavityGaussianMarks S))
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) R) hl measurable_id
  rw [Measure.map_id, cavity_marked_leaf_sum_law n b hb S hS] at he
  rw [show (fun p : (ℕ → NoiseLeaf (EuclideanSpace ℝ (Fin d)) n) ×
      EuclideanSpace ℝ (Fin d) => cavityLeafSum n 0 (p.1 0) + p.2) =
      (fun p => p.1 + p.2) ∘ Prod.map (fun σ => cavityLeafSum n 0 (σ 0)) id from rfl,
    ← Measure.map_map (by fun_prop) (hl.prodMap measurable_id), ← he]
  exact cavity_gaussian_add_law _ R
    (Matrix.posSemidef_sum Finset.univ (fun i _ => hS i)) hR

end InvariantIsing

end

end OAI
