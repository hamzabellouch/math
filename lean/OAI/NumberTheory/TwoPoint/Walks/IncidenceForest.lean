import OAI.NumberTheory.TwoPoint.Walks.ForestGeometry
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace OAI

/-!
# Incidence forests for independent affine directions

An edge is cut by the coordinate of its line direction. All other lines
preserve this coordinate. On the selected line the coordinate determines
the point, so the deleted edge is the only crossing of the cut.
-/

namespace TwoPointCorrelations

open SimpleGraph

variable {K ι V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Linear coordinates on an independent family, extended to the ambient space. -/
theorem independent_coordinate_functionals [DecidableEq ι] (d : ι → V) (hd : LinearIndependent K d) :
    ∃ φ : ι → V →ₗ[K] K, ∀ i j, φ i (d j) = if i = j then 1 else 0 := by
  classical
  obtain ⟨g, hg⟩ := (Finsupp.linearCombination K d).exists_leftInverse_of_injective
    (linearIndependent_iff_ker.mp hd)
  refine ⟨fun i => (Finsupp.lapply i).comp g, ?_⟩
  intro i j
  have hj := LinearMap.congr_fun hg (Finsupp.single j 1)
  have hdj : g (d j) = Finsupp.single j 1 := by
    simpa only [LinearMap.comp_apply, Finsupp.linearCombination_single, one_smul,
      LinearMap.id_apply] using hj
  simp only [LinearMap.comp_apply, Finsupp.lapply_apply, hdj, Finsupp.single_apply]
  simp only [eq_comm]

/-- Line vertices and point vertices are distinct, even when their types coincide. -/
def affineIncidenceGraph (anchor d : ι → V) : SimpleGraph (ι ⊕ V) where
  Adj
    | .inl i, .inr x => ∃ t : K, x = anchor i + t • d i
    | .inr x, .inl i => ∃ t : K, x = anchor i + t • d i
    | _, _ => False
  symm := ⟨by
    intro x y h
    cases x <;> cases y <;> exact h⟩
  loopless := ⟨by intro x; cases x <;> exact id⟩

private theorem coordinate_injective_on_line (anchor d : ι → V)
    (φ : V →ₗ[K] K) (i : ι) (hφ : φ (d i) = 1)
    {x y : V} (hx : ∃ t : K, x = anchor i + t • d i)
    (hy : ∃ t : K, y = anchor i + t • d i) (hxy : φ x = φ y) : x = y := by
  obtain ⟨s, rfl⟩ := hx
  obtain ⟨t, rfl⟩ := hy
  have hst : s = t := by
    simpa only [map_add, map_smul, hφ, smul_eq_mul, mul_one, add_right_inj] using hxy
  rw [hst]

private def edgeSide (anchor : ι → V) (φ : V →ₗ[K] K) (i : ι) (x : V) :
    (ι ⊕ V) → Prop
  | .inl j => j ≠ i ∧ φ (anchor j) = φ x
  | .inr y => φ y = φ x

private theorem edgeSide_incidence [DecidableEq ι] (anchor d : ι → V) (φ : V →ₗ[K] K)
    (i : ι) (hφ : ∀ j, φ (d j) = if i = j then 1 else 0)
    (x : V) (hx : ∃ t : K, x = anchor i + t • d i)
    (j : ι) (y : V) (hy : ∃ t : K, y = anchor j + t • d j)
    (hne : ¬ (j = i ∧ y = x)) :
    edgeSide anchor φ i x (.inl j) ↔ edgeSide anchor φ i x (.inr y) := by
  classical
  by_cases hji : j = i
  · subst j
    have hneq : φ y ≠ φ x := by
      intro heq
      exact hne ⟨rfl, coordinate_injective_on_line anchor d φ i (by simpa using hφ i)
        hy hx heq⟩
    simp [edgeSide, hneq]
  · obtain ⟨t, rfl⟩ := hy
    have hdir : φ (d j) = 0 := by simp [hφ, Ne.symm hji]
    simp [edgeSide, hji, map_add, map_smul, hdir]

/-- Every incidence edge is a bridge when line directions are independent. -/
theorem affineIncidenceGraph_edge_isBridge (anchor d : ι → V)
    (hd : LinearIndependent K d) (i : ι) (x : V)
    (hx : ∃ t : K, x = anchor i + t • d i) :
    (affineIncidenceGraph (K := K) anchor d).IsBridge s(Sum.inl i, Sum.inr x) := by
  classical
  obtain ⟨φ, hφ⟩ := independent_coordinate_functionals d hd
  let G := affineIncidenceGraph (K := K) anchor d
  let H := G.deleteEdges {s(Sum.inl i, Sum.inr x)}
  let side := edgeSide anchor (φ i) i x
  have hinv : ∀ {u v}, H.Adj u v → (side u ↔ side v) := by
    intro u v huv
    obtain ⟨huv, hdel⟩ := deleteEdges_adj.mp huv
    have hne : s(u, v) ≠ s(Sum.inl i, Sum.inr x) := by
      simpa only [Set.mem_singleton_iff] using hdel
    cases u with
    | inl j =>
      cases v with
      | inl k => exact huv.elim
      | inr y =>
        apply edgeSide_incidence anchor d (φ i) i (hφ i) x hx j y huv
        rintro ⟨rfl, rfl⟩
        exact hne rfl
    | inr y =>
      cases v with
      | inl j =>
        apply Iff.symm
        apply edgeSide_incidence anchor d (φ i) i (hφ i) x hx j y huv
        rintro ⟨rfl, rfl⟩
        exact hne (by simp only [Sym2.eq_swap])
      | inr z => exact huv.elim
  have hwalk : ∀ {u v} (w : H.Walk u v), side u ↔ side v := by
    intro u v w
    induction w with
    | nil => rfl
    | cons h w ih => exact (hinv h).trans ih
  apply isBridge_iff.mpr
  rintro ⟨w⟩
  have hf := (hwalk w).mpr (show side (Sum.inr x) by rfl)
  exact hf.1 rfl

/-- One affine line per independent direction has an acyclic incidence graph. -/
theorem affineIncidenceGraph_isAcyclic (anchor d : ι → V)
    (hd : LinearIndependent K d) : (affineIncidenceGraph (K := K) anchor d).IsAcyclic := by
  apply isAcyclic_iff_forall_adj_isBridge.mpr
  intro u v huv
  cases u with
  | inl i =>
    cases v with
    | inl j => exact huv.elim
    | inr x => exact affineIncidenceGraph_edge_isBridge anchor d hd i x huv
  | inr x =>
    cases v with
    | inl i =>
      simpa only [Sym2.eq_swap] using affineIncidenceGraph_edge_isBridge anchor d hd i x huv
    | inr y => exact huv.elim

/-- A run sequence without immediate reversal is recovered from its two endpoints. -/
theorem incidence_walk_unique (anchor d : ι → V) (hd : LinearIndependent K d)
    {u v : ι ⊕ V} (p q : (affineIncidenceGraph (K := K) anchor d).Walk u v)
    (hp : List.IsChain (· ≠ ·) p.edges) (hq : List.IsChain (· ≠ ·) q.edges) : p = q := by
  have hG := affineIncidenceGraph_isAcyclic anchor d hd
  have hp' := (hG.isPath_iff_isChain p).mpr hp
  have hq' := (hG.isPath_iff_isChain q).mpr hq
  exact Subtype.mk.inj (hG.subsingleton_path u v |>.elim ⟨p, hp'⟩ ⟨q, hq'⟩)

end TwoPointCorrelations

end OAI
