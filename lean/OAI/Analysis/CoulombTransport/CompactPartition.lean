import Mathlib

namespace OAI

universe uX uIndex

noncomputable section

open Set MeasureTheory Metric

namespace Problem356

/-- Disjointification preserves measurability for finite ordered index sets. -/
theorem measurableSet_disjointed_fin {X : Type uX} [MeasurableSpace X]
    {n : ℕ} {A : Fin n → Set X} (hA : ∀ i, MeasurableSet (A i)) (i : Fin n) :
    MeasurableSet (disjointed A i) := by
  exact disjointedRec (fun _ _ ht => ht.diff (hA _)) (hA i)

/-- A compact metric set admits a finite Borel partition into sets of arbitrarily
small diameter. Empty cells are permitted, so the indexing is uniform. -/
theorem exists_compact_small_partition {X : Type uX} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] {K : Set X} (hK : IsCompact K)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (n : ℕ) (A : Fin n → Set X),
      (∀ i, MeasurableSet (A i)) ∧
      Pairwise (fun i j => Disjoint (A i) (A j)) ∧
      (⋃ i, A i) = K ∧
      (∀ i, A i ⊆ K) ∧
      (∀ i, ∀ x ∈ A i, ∀ y ∈ A i, dist x y < δ) := by
  classical
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun x : X => ball x (δ / 2)) (fun _ => isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨x, mem_ball_self (half_pos hδ)⟩)
  let e : s ≃ Fin (Fintype.card s) := Fintype.equivFin s
  let B : Fin (Fintype.card s) → Set X := fun i => K ∩ ball (e.symm i).val (δ / 2)
  have hB : ∀ i, MeasurableSet (B i) := fun _ =>
    hK.measurableSet.inter measurableSet_ball
  have hCover : (⋃ i, B i) = K := by
    apply Subset.antisymm
    · exact iUnion_subset fun i => inter_subset_left
    · intro x hx
      obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hs hx)
      refine mem_iUnion.mpr ⟨e ⟨y, hy⟩, hx, ?_⟩
      simpa only [Equiv.symm_apply_apply] using hxy
  refine ⟨Fintype.card s, disjointed B, measurableSet_disjointed_fin hB,
    disjoint_disjointed B, ?_, ?_, ?_⟩
  · rw [iUnion_disjointed, hCover]
  · intro i
    exact (disjointed_subset B i).trans inter_subset_left
  · intro i x hx y hy
    have hx' := (disjointed_subset B i hx).2
    have hy' := (disjointed_subset B i hy).2
    calc
      dist x y ≤ dist x (e.symm i).val + dist (e.symm i).val y := dist_triangle _ _ _
      _ < δ / 2 + δ / 2 := add_lt_add (mem_ball.mp hx') (by simpa only [dist_comm] using (mem_ball.mp hy'))
      _ = δ := by ring

/-- The small cells may simultaneously be chosen inside a prescribed finite
family of pairwise disjoint compact components. -/
theorem exists_compact_component_partition {X : Type uX} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] {ι : Type uIndex} [Fintype ι]
    (K : ι → Set X) (hK : ∀ a, IsCompact (K a))
    (hDisjoint : Pairwise (fun a b => Disjoint (K a) (K b)))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (n : ℕ) (A : ι × Fin n → Set X),
      (∀ p, MeasurableSet (A p)) ∧
      Pairwise (fun p q => Disjoint (A p) (A q)) ∧
      (⋃ p, A p) = ⋃ a, K a ∧
      (∀ p, A p ⊆ K p.1) ∧
      (∀ p, ∀ x ∈ A p, ∀ y ∈ A p, dist x y < δ) := by
  classical
  obtain ⟨n, B, hMeas, hPair, hCover, hSub, hDist⟩ :=
    exists_compact_small_partition (isCompact_iUnion hK) hδ
  let A : ι × Fin n → Set X := fun p => K p.1 ∩ B p.2
  refine ⟨n, A, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    exact (hK p.1).measurableSet.inter (hMeas p.2)
  · intro p q hpq
    by_cases hfirst : p.1 = q.1
    · have hsecond : p.2 ≠ q.2 := by
        intro hsecond
        exact hpq (Prod.ext hfirst hsecond)
      exact (hPair hsecond).mono inter_subset_right inter_subset_right
    · exact (hDisjoint hfirst).mono inter_subset_left inter_subset_left
  · apply Subset.antisymm
    · intro x hx
      obtain ⟨p, hp⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨p.1, hp.1⟩
    · intro x hx
      obtain ⟨a, ha⟩ := mem_iUnion.mp hx
      have hxB : x ∈ ⋃ i, B i := by
        rw [hCover]
        exact mem_iUnion.mpr ⟨a, ha⟩
      obtain ⟨i, hi⟩ := mem_iUnion.mp hxB
      exact mem_iUnion.mpr ⟨(a, i), ha, hi⟩
  · intro p
    exact inter_subset_left
  · intro p x hx y hy
    exact hDist p.2 x hx.2 y hy.2

end Problem356

end

end OAI
