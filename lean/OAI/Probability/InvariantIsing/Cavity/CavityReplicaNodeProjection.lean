import OAI.Probability.InvariantIsing.Cavity.CavityGaussianNodePrior
import OAI.Probability.InvariantIsing.Cavity.CavityGaussianNodeCovariance

namespace OAI

/-! The finite set of Gaussian nodes visited by a tuple of cavity leaves.
Each replica keeps the common root and shared edges, and receives its own
ordinary terminal residual. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavity_nodeAt_injective (n : ℕ) (v : LabeledLeaf n) :
    Function.Injective (nodeAt n v) := by
  intro i j h
  apply Fin.ext
  have hl := congrArg (fun a => (nodeAddress n a).length) h
  simpa only [nodeAddress_nodeAt_length] using hl

def cavityReplicaNodePath {r : ℕ} (n : ℕ) (v : LabeledLeaf n) (i : Fin r) :
    Finset (CavityReplicaNode n r) := by
  classical
  exact insert (Sum.inr i)
    (Finset.univ.image (fun k : Fin (n + 1) => Sum.inl (nodeAt n v k)))

def cavityReplicaNodeSupport {r : ℕ} (n : ℕ) (σ : Fin r → LabeledLeaf n) :
    Finset (CavityReplicaNode n r) := by
  classical
  exact Finset.univ.biUnion (fun i => cavityReplicaNodePath n (σ i) i)

def cavityReplicaNodeWeight {r : ℕ} (n : ℕ) (σ : Fin r → LabeledLeaf n)
    (i : Fin r) (a : cavityReplicaNodeSupport n σ) : ℝ := by
  classical
  exact if (a : CavityReplicaNode n r) ∈ cavityReplicaNodePath n (σ i) i then 1 else 0

lemma cavityReplicaNodePath_subset {r : ℕ} (n : ℕ) (σ : Fin r → LabeledLeaf n)
    (i : Fin r) : cavityReplicaNodePath n (σ i) i ⊆ cavityReplicaNodeSupport n σ := by
  classical
  intro a ha
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ha⟩

lemma cavity_replica_node_sum {r d : ℕ} (n : ℕ) (σ : Fin r → LabeledLeaf n)
    (z : CavityReplicaNode n r → EuclideanSpace ℝ (Fin d)) (i : Fin r) (j : Fin d) :
    cavityGaussianNodeSum (cavityReplicaNodeWeight n σ)
      (fun a => z a) (i, j) =
        (z (.inl none)) j + (∑ k : Fin n, z (.inl (some (edgeAt n (σ i) k))) j) +
          z (.inr i) j := by
  classical
  change (∑ a : cavityReplicaNodeSupport n σ,
    (if (a : CavityReplicaNode n r) ∈ cavityReplicaNodePath n (σ i) i then (1 : ℝ) else 0) *
      z a j) = _
  have he : (∑ a : cavityReplicaNodeSupport n σ,
      (if (a : CavityReplicaNode n r) ∈ cavityReplicaNodePath n (σ i) i then (1 : ℝ) else 0) *
        z a j) = ∑ a ∈ cavityReplicaNodeSupport n σ,
      (if a ∈ cavityReplicaNodePath n (σ i) i then (1 : ℝ) else 0) * z a j :=
    Finset.sum_coe_sort (cavityReplicaNodeSupport n σ)
      (fun a : CavityReplicaNode n r =>
        (if a ∈ cavityReplicaNodePath n (σ i) i then (1 : ℝ) else 0) * z a j)
  rw [he]
  simp_rw [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  have hf : (cavityReplicaNodeSupport n σ).filter
      (fun a => a ∈ cavityReplicaNodePath n (σ i) i) = cavityReplicaNodePath n (σ i) i := by
    ext a
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨cavityReplicaNodePath_subset n σ i h, h⟩⟩
  rw [hf, cavityReplicaNodePath, Finset.sum_insert]
  · rw [Finset.sum_image]
    · rw [Fin.sum_univ_succ]
      simp only [nodeAt_zero, nodeAt_succ]
      ring
    · intro k _ l _ hkl
      exact cavity_nodeAt_injective n (σ i) (Sum.inl.inj hkl)
  · simp

/-- The node representation is pointwise the original root-plus-forest
field, including the independent residual of each replica. -/
theorem cavity_replica_node_field {r d : ℕ} (n : ℕ) (σ : Fin r → LabeledLeaf n)
    (T : LabeledTree n)
    (p : (EuclideanSpace ℝ (Fin d) × (ForestVertex n → EuclideanSpace ℝ (Fin d))) ×
      (Fin r → EuclideanSpace ℝ (Fin d))) :
    cavityGaussianNodeSum (cavityReplicaNodeWeight n σ)
      (fun a => cavityReplicaNodeJoin n r p a) =
      WithLp.toLp 2 (fun q : Fin r × Fin d =>
        (cavityLeafSum n p.1.1 (labeledNoiseLeaf _ n
          (T, markForestOfCoords _ n p.1.2) (σ q.1)) + p.2 q.1) q.2) := by
  ext q
  change cavityGaussianNodeSum (cavityReplicaNodeWeight n σ)
    (fun a => cavityReplicaNodeJoin n r p a) q =
      (cavityLeafSum n p.1.1 (labeledNoiseLeaf _ n
        (T, markForestOfCoords _ n p.1.2) (σ q.1)) + p.2 q.1) q.2
  rw [cavity_replica_node_sum, cavity_labeled_leaf_sum]
  simp [cavityReplicaNodeJoin]

def cavityReplicaGaussianCovariance {r d : ℕ} (n : ℕ)
    (S₀ R : Matrix (Fin d) (Fin d) ℝ) (S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (σ : Fin r → LabeledLeaf n) : Matrix (Fin r × Fin d) (Fin r × Fin d) ℝ :=
  cavityGaussianNodeCovariance
    (fun a : cavityReplicaNodeSupport n σ => cavityReplicaNodeCovariance n r S₀ R S a)
    (cavityReplicaNodeWeight n σ)

/-- Joint law of the actual cavity fields for any fixed tuple of leaves.
The same root is retained in every replica; ordinary residuals are independent. -/
theorem cavity_replica_gaussian_field_law {r d : ℕ} (n : ℕ)
    (S₀ R : Matrix (Fin d) (Fin d) ℝ) (S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hS₀ : S₀.PosSemidef) (hR : R.PosSemidef) (hS : ∀ i, (S i).PosSemidef)
    (T : LabeledTree n) (σ : Fin r → LabeledLeaf n) :
    (((multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
      (Measure.infinitePi (fun v : ForestVertex n => multivariateGaussian
        (0 : EuclideanSpace ℝ (Fin d)) (S (forestVertexDepth n v))))).prod
          (Measure.pi (fun _ : Fin r => multivariateGaussian
            (0 : EuclideanSpace ℝ (Fin d)) R))).map
      (fun p => WithLp.toLp 2 (fun q : Fin r × Fin d =>
        (cavityLeafSum n p.1.1 (labeledNoiseLeaf _ n
          (T, markForestOfCoords _ n p.1.2) (σ q.1)) + p.2 q.1) q.2)) =
      multivariateGaussian 0 (cavityReplicaGaussianCovariance n S₀ R S σ) := by
  classical
  let V := cavityReplicaNodeSupport n σ
  let C := cavityReplicaNodeCovariance n r S₀ R S
  let w := cavityReplicaNodeWeight n σ
  let F : (CavityReplicaNode n r → EuclideanSpace ℝ (Fin d)) →
      EuclideanSpace ℝ (Fin r × Fin d) :=
    fun z => cavityGaussianNodeSum w (fun a : V => z a)
  have hC (a : CavityReplicaNode n r) : (C a).PosSemidef := by
    cases a with
    | inl a => cases a with
      | none => exact hS₀
      | some a => exact hS _
    | inr a => exact hR
  have hQ := cavityGaussianNodeCovariance_posSemidef (fun a : V => C a)
    (fun a => hC a) w
  have hp := cavity_gaussian_finite_node_law
    (fun a : V => (a : CavityReplicaNode n r)) Subtype.val_injective C hC w
    (cavityReplicaGaussianCovariance n S₀ R S σ) hQ (fun _ _ => rfl)
  have hF : Measurable F := by
    unfold F cavityGaussianNodeSum
    fun_prop
  rw [← cavity_replica_node_prior_law n r S₀ R S,
    Measure.map_map hF (measurable_cavityReplicaNodeJoin n r)] at hp
  have he : F ∘ cavityReplicaNodeJoin (d := d) n r =
      fun p => WithLp.toLp 2 (fun q : Fin r × Fin d =>
        (cavityLeafSum n p.1.1 (labeledNoiseLeaf _ n
          (T, markForestOfCoords _ n p.1.2) (σ q.1)) + p.2 q.1) q.2) := by
    funext p
    exact cavity_replica_node_field n σ T p
  simpa only [he] using hp

end InvariantIsing

end

end OAI
