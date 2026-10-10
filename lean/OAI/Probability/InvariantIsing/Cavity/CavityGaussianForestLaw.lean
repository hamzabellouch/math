import OAI.Probability.InvariantIsing.Cavity.CavityGaussianNodeLaw
import OAI.Probability.InvariantIsing.Cavity.CavityOneReplicaPath
import OAI.Probability.InvariantIsing.Cavity.CavityProjectedForest

namespace OAI

/-! Finite restrictions of the independent Gaussian forest, and the
literal sum of its marks along a labeled cavity leaf. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix BigOperators

namespace InvariantIsing

lemma cavity_labeled_leaf_sum {d : ℕ} (n : ℕ) (T : LabeledTree n)
    (g : ForestVertex n → EuclideanSpace ℝ (Fin d)) (v : LabeledLeaf n)
    (s : EuclideanSpace ℝ (Fin d)) :
    cavityLeafSum n s (labeledNoiseLeaf _ n (T, markForestOfCoords _ n g) v) =
      s + ∑ i : Fin n, g (edgeAt n v i) := by
  rw [cavityLeafSum_eq_mark_sum]
  simp_rw [noiseLeafMark_labeled]

/-- A finite set of distinct nodes can be sampled from the full product
law before taking any linear replica projections. -/
theorem cavity_gaussian_finite_node_law {A J : Type*} [Fintype J] [DecidableEq J]
    {d r : ℕ} (e : J → A) (he : Function.Injective e)
    (S : A → Matrix (Fin d) (Fin d) ℝ) (hS : ∀ a, (S a).PosSemidef)
    (w : Fin r → J → ℝ)
    (Q : Matrix (Fin r × Fin d) (Fin r × Fin d) ℝ) (hQ : Q.PosSemidef)
    (hcov : ∀ p q, Q p q = ∑ a, w p.1 a * w q.1 a * S (e a) p.2 q.2) :
    (Measure.infinitePi (fun a => multivariateGaussian
      (0 : EuclideanSpace ℝ (Fin d)) (S a))).map
        (fun z => cavityGaussianNodeSum w (fun a => z (e a))) =
          multivariateGaussian 0 Q := by
  have hm : Measurable (fun z : J → EuclideanSpace ℝ (Fin d) =>
      cavityGaussianNodeSum w z) := by
    unfold cavityGaussianNodeSum
    fun_prop
  rw [show (fun z : A → EuclideanSpace ℝ (Fin d) =>
      cavityGaussianNodeSum w (fun a => z (e a))) =
      cavityGaussianNodeSum w ∘ (fun z a => z (e a)) from rfl,
    ← Measure.map_map hm (by fun_prop),
    Measure.map_infinitePi_infinitePi_of_inj he, Measure.infinitePi_eq_pi]
  exact cavity_gaussian_node_sum_law (fun a => S (e a)) (fun a => hS (e a)) w Q hQ hcov

end InvariantIsing

end

end OAI
