import OAI.NumberTheory.DukePrimeDegree.Dynamics.RootOrbitRebase

namespace OAI

/-!
# Enlarging a null set to avoid it along every conditional root leaf

Iterating the ambient-to-leaf null-set implication gives one measurable
null set whose complement is leafwise conull at every remaining point.
This lets the commutator construction choose all of its vertices outside
the same exceptional set.
-/

noncomputable section
open Set Filter MeasureTheory

namespace DukePrimeDegree
open PrimeDegreePackets

theorem enlarge_nullset_leafwise
    {X T I : Type*} [MeasurableSpace X] [MeasurableSpace T] [Countable I]
    (μ : Measure X) (ν : I → X → Measure T) (R : I → X → T → X)
    (hdis : ∀ i {P : X → Prop}, (∀ᵐ x ∂μ, P x) →
      ∀ᵐ x ∂μ, ∀ᵐ t ∂ν i x, P (R i x t))
    (N : Set X) (hN : MeasurableSet N) (hNzero : μ N = 0) :
    ∃ M : Set X, MeasurableSet M ∧ μ M = 0 ∧ N ⊆ M ∧
      ∀ x ∉ M, ∀ i, ∀ᵐ t ∂ν i x, R i x t ∉ M := by
  let S := {A : Set X // MeasurableSet A ∧ μ A = 0}
  have hstep (A : S) : ∃ B : S, A.val ⊆ B.val ∧
      ∀ x ∉ B.val, ∀ i, ∀ᵐ t ∂ν i x, R i x t ∉ A.val := by
    have ha : ∀ᵐ x ∂μ, x ∉ A.val := by
      rw [ae_iff]
      simpa only [not_not, Set.ofPred_mem_eq] using A.prop.2
    have hall : ∀ᵐ x ∂μ, ∀ i, ∀ᵐ t ∂ν i x, R i x t ∉ A.val :=
      ae_all_iff.mpr fun i => hdis i ha
    obtain ⟨B, hbad, hB, hBzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hall)
    refine ⟨⟨A.val ∪ B, A.prop.1.union hB, measure_union_null A.prop.2 hBzero⟩,
      subset_union_left, ?_⟩
    intro x hx
    by_contra h
    exact hx (Or.inr (hbad h))
  let next (A : S) : S := (hstep A).choose
  let A : ℕ → S := fun m => Nat.rec ⟨N, hN, hNzero⟩ (fun _ prev => next prev) m
  have hAstep (m : ℕ) : ∀ x ∉ (A (m + 1)).val, ∀ i,
      ∀ᵐ t ∂ν i x, R i x t ∉ (A m).val :=
    (hstep (A m)).choose_spec.2
  let M := ⋃ m : ℕ, (A m).val
  refine ⟨M, MeasurableSet.iUnion (fun m => (A m).prop.1),
    measure_iUnion_null (fun m => (A m).prop.2), ?_, ?_⟩
  · exact fun x hx => mem_iUnion.mpr ⟨0, hx⟩
  · intro x hx i
    have ha (m : ℕ) : ∀ᵐ t ∂ν i x, R i x t ∉ (A m).val :=
      hAstep m x (fun h => hx (mem_iUnion.mpr ⟨m + 1, h⟩)) i
    filter_upwards [ae_all_iff.mpr ha] with t ht
    simpa only [M, mem_iUnion, not_exists] using ht

theorem enlarge_nullset_all_roots
    (d : ℕ) (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (N : Set (X (d + 1))) (hN : MeasurableSet N) (hNzero : μ N = 0) :
    ∃ M : Set (X (d + 1)), MeasurableSet M ∧ μ M = 0 ∧ N ⊆ M ∧
      ∀ x ∉ M, ∀ (a b : Fin (d + 1)) (hab : a ≠ b),
        ∀ᵐ t ∂intrinsicRootLeaf hab μ x,
          rightAction x (Matrix.SpecialLinearGroup.transvection hab t) ∉ M := by
  let I := {p : Fin (d + 1) × Fin (d + 1) // p.1 ≠ p.2}
  let ν : I → X (d + 1) → Measure ℝ := fun q => intrinsicRootLeaf q.prop μ
  let R : I → X (d + 1) → ℝ → X (d + 1) :=
    fun q x t => rightAction x (Matrix.SpecialLinearGroup.transvection q.prop t)
  have hd (q : I) {P : X (d + 1) → Prop} (hp : ∀ᵐ x ∂μ, P x) :
      ∀ᵐ x ∂μ, ∀ᵐ t ∂ν q x, P (R q x t) := by
    apply ae_intrinsicRootLeaf_of_ambient q.prop μ _ hp
    exact (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx q.val.1 q.val.2 q.prop
  obtain ⟨M, hM, hMzero, hNM, hleaf⟩ := enlarge_nullset_leafwise μ ν R hd N hN hNzero
  exact ⟨M, hM, hMzero, hNM, fun x hx a b hab => hleaf x hx ⟨(a, b), hab⟩⟩

end DukePrimeDegree

end

end OAI
