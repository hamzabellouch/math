import OAI.Probability.InvariantIsing.Cavity.CavityReplicaNodeProjection

namespace OAI

/-! Shared-prefix covariance of the actual Gaussian cavity replica fields. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavity_nodeAt_eq_iff (n : ℕ) (v w : LabeledLeaf n) (i j : Fin (n + 1)) :
    nodeAt n v i = nodeAt n w j ↔
      i = j ∧ (i : ℕ) ≤ labeledCommonDepth n v w := by
  constructor
  · intro h
    have hij : i = j := by
      apply Fin.ext
      have he := congrArg (fun a => (nodeAddress n a).length) h
      simpa only [nodeAddress_nodeAt_length] using he
    subst j
    refine ⟨rfl, ?_⟩
    apply (labeled_prefix_eq_iff n v w (Nat.le_of_lt_succ i.isLt)).mp
    simpa only [nodeAddress_nodeAt] using congrArg (nodeAddress n) h
  · rintro ⟨rfl, h⟩
    apply nodeAddress_injective n
    simpa only [nodeAddress_nodeAt] using
      (labeled_prefix_eq_iff n v w (Nat.le_of_lt_succ i.isLt)).mpr h

lemma cavity_edgeAt_depth (n : ℕ) (v : LabeledLeaf n) (i : Fin n) :
    forestVertexDepth n (edgeAt n v i) = i := by
  have he := nodeAddress_nodeAt_length n v i.succ
  rw [nodeAt_succ, nodeAddress_length_some] at he
  exact Nat.add_right_cancel he

lemma cavity_nodeAt_mem_replicaPath {r : ℕ} (n : ℕ)
    (v w : LabeledLeaf n) (j : Fin r) (i : Fin (n + 1)) :
    (Sum.inl (nodeAt n v i) : CavityReplicaNode n r) ∈ cavityReplicaNodePath n w j ↔
      (i : ℕ) ≤ labeledCommonDepth n v w := by
  classical
  simp only [cavityReplicaNodePath, Finset.mem_insert, Sum.inl.injEq,
    Sum.inl_ne_inr, false_or, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, hk⟩
    exact ((cavity_nodeAt_eq_iff n v w i k).mp hk.symm).2
  · intro hi
    exact ⟨i, ((cavity_nodeAt_eq_iff n v w i i).mpr ⟨rfl, hi⟩).symm⟩

lemma cavityReplicaGaussianCovariance_entry {r d : ℕ} (n : ℕ)
    (S₀ R : Matrix (Fin d) (Fin d) ℝ) (S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (σ : Fin r → LabeledLeaf n) (i j : Fin r) (a b : Fin d) :
    cavityReplicaGaussianCovariance n S₀ R S σ (i, a) (j, b) =
      S₀ a b + (∑ k : Fin n,
        if (k : ℕ) + 1 ≤ labeledCommonDepth n (σ i) (σ j) then S k a b else 0) +
          if i = j then R a b else 0 := by
  classical
  let V := cavityReplicaNodeSupport n σ
  let C := cavityReplicaNodeCovariance n r S₀ R S
  change (∑ v : V, cavityReplicaNodeWeight n σ i v *
    cavityReplicaNodeWeight n σ j v * C v a b) = _
  simp only [cavityReplicaNodeWeight]
  rw [Finset.sum_coe_sort V (fun v : CavityReplicaNode n r =>
    (if v ∈ cavityReplicaNodePath n (σ i) i then (1 : ℝ) else 0) *
    (if v ∈ cavityReplicaNodePath n (σ j) j then (1 : ℝ) else 0) * C v a b)]
  have hf (v : CavityReplicaNode n r) :
      (if v ∈ cavityReplicaNodePath n (σ i) i then (1 : ℝ) else 0) *
      (if v ∈ cavityReplicaNodePath n (σ j) j then 1 else 0) * C v a b =
      if v ∈ cavityReplicaNodePath n (σ i) i then
        (if v ∈ cavityReplicaNodePath n (σ j) j then C v a b else 0) else 0 := by
    split_ifs <;> simp
  simp_rw [hf]
  rw [← Finset.sum_filter]
  have hs : V.filter (fun v => v ∈ cavityReplicaNodePath n (σ i) i) =
      cavityReplicaNodePath n (σ i) i := by
    ext v
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨cavityReplicaNodePath_subset n σ i h, h⟩⟩
  rw [hs, cavityReplicaNodePath, Finset.sum_insert]
  · rw [Finset.sum_image]
    · simp_rw [cavity_nodeAt_mem_replicaPath]
      rw [Fin.sum_univ_succ]
      simp only [nodeAt_zero, nodeAt_succ, Fin.val_zero, zero_le,
        ite_true, Fin.val_succ, C, cavityReplicaNodeCovariance, Sum.elim_inl,
        Option.elim_none, Option.elim_some, cavity_edgeAt_depth]
      have hr : (if (Sum.inr i : CavityReplicaNode n r) ∈ cavityReplicaNodePath n (σ j) j
          then cavityReplicaNodeCovariance n r S₀ R S (.inr i) a b else 0) =
          if i = j then R a b else 0 := by
        simp [cavityReplicaNodePath, cavityReplicaNodeCovariance]
      change (if (Sum.inr i : CavityReplicaNode n r) ∈ cavityReplicaNodePath n (σ j) j
          then cavityReplicaNodeCovariance n r S₀ R S (.inr i) a b else 0) +
        (S₀ a b + ∑ k : Fin n,
          if (k : ℕ) + 1 ≤ labeledCommonDepth n (σ i) (σ j) then S k a b else 0) = _
      rw [hr]
      ring
    · intro k _ l _ hkl
      exact cavity_nodeAt_injective n (σ i) (Sum.inl.inj hkl)
  · simp

end InvariantIsing

end

end OAI
