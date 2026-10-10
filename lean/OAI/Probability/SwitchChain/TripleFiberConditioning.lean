import OAI.Probability.SwitchChain.PairInternalRedundancy

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem315.PairResampling
attribute [local instance] Classical.propDecidable

def triangleEdgeCount {n : ℕ} (G : SimpleGraph (Fin n)) (i j k : Fin n) : ℕ :=
  (if G.Adj i j then 1 else 0) + (if G.Adj i k then 1 else 0) +
    (if G.Adj j k then 1 else 0)

theorem triple_internal_degree_eq {n : ℕ} {d : Fin n → ℕ}
    (G H : GraphState n d) (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hrow : ∀ w, w ∉ ({i, j, k} : Finset (Fin n)) →
      (G.val.Adj i w ↔ H.val.Adj i w)) :
    (if G.val.Adj i j then 1 else 0) + (if G.val.Adj i k then 1 else 0) =
      (if H.val.Adj i j then 1 else 0) + (if H.val.Adj i k then 1 else 0) := by
  classical
  let T : Finset (Fin n) := {i, j, k}
  have hout : ((Finset.univ.filter (G.val.Adj i)).filter (fun w => w ∉ T)) =
      ((Finset.univ.filter (H.val.Adj i)).filter (fun w => w ∉ T)) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_congr_left (fun hw => hrow w hw)
  have hg := degree_eq_inside_add_outside G.val T i
  have hh := degree_eq_inside_add_outside H.val T i
  have hd : graphDegree G.val i = graphDegree H.val i := (G.property i).trans (H.property i).symm
  rw [hg, hh, hout] at hd
  have hin := Nat.add_right_cancel hd
  have hcalc (K : SimpleGraph (Fin n)) :
      (T.filter (K.Adj i)).card =
        (if K.Adj i j then 1 else 0) + (if K.Adj i k then 1 else 0) := by
    rw [Finset.card_filter]
    dsimp [T]
    rw [Finset.sum_insert (by simp [hij, hik]),
      Finset.sum_insert (by simpa using hjk), Finset.sum_singleton]
    simp
  simpa only [hcalc] using hin

theorem opposite_edge_eq_of_triangle_data {n : ℕ} {d : Fin n → ℕ}
    (G H : GraphState n d) (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (he : triangleEdgeCount G.val i j k = triangleEdgeCount H.val i j k)
    (hrow : ∀ w, w ∉ ({i, j, k} : Finset (Fin n)) →
      (G.val.Adj i w ↔ H.val.Adj i w)) :
    G.val.Adj j k ↔ H.val.Adj j k := by
  have hd := triple_internal_degree_eq G H i j k hij hik hjk hrow
  unfold triangleEdgeCount at he
  by_cases hg : G.val.Adj j k <;> by_cases hh : H.val.Adj j k <;>
    simp_all

theorem sameFiber_pair_iff_exterior_row {n : ℕ} {d : Fin n → ℕ}
    (G H : GraphState n d) (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hout : ∀ u, u ∉ ({i, j, k} : Finset (Fin n)) →
      ∀ v, v ∉ ({i, j, k} : Finset (Fin n)) →
        (G.val.Adj u v ↔ H.val.Adj u v))
    (he : triangleEdgeCount G.val i j k = triangleEdgeCount H.val i j k) :
    SameFiber ({j, k} : Finset (Fin n)) G.val H.val ↔
      ∀ w, w ∉ ({i, j, k} : Finset (Fin n)) →
        (G.val.Adj i w ↔ H.val.Adj i w) := by
  classical
  constructor
  · intro h w hw
    have hi : i ∉ ({j, k} : Finset (Fin n)) := by simp [hij, hik]
    have hw' : w ∉ ({j, k} : Finset (Fin n)) := by
      intro hmem
      exact hw (Finset.mem_insert_of_mem hmem)
    exact h.1 i hi w hw'
  · intro hrow
    have hop := opposite_edge_eq_of_triangle_data G H i j k hij hik hjk he hrow
    apply (sameFiber_iff_outside_inside _ G H).mpr
    constructor
    · intro u hu v hv
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hu hv
      by_cases hui : u = i
      · subst u
        by_cases hvi : v = i
        · subst v
          simp
        · exact hrow v (by simp [hvi, hv.1, hv.2])
      · by_cases hvi : v = i
        · subst v
          have h := hrow u (by simp [hui, hu.1, hu.2])
          exact ⟨fun hG => (h.mp hG.symm).symm,
            fun hH => (h.mpr hH.symm).symm⟩
        · exact hout u (by simp [hui, hu.1, hu.2]) v (by simp [hvi, hv.1, hv.2])
    · intro u hu v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · simp
      · exact hop
      · exact ⟨fun hG => (hop.mp hG.symm).symm,
          fun hH => (hop.mpr hH.symm).symm⟩
      · simp

theorem sameFiber_pair_iff_exterior_row_of_outside {n : ℕ} {d : Fin n → ℕ}
    (G H : GraphState n d) (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hout : ∀ u, u ∉ ({i, j, k} : Finset (Fin n)) →
      ∀ v, v ∉ ({i, j, k} : Finset (Fin n)) →
        (G.val.Adj u v ↔ H.val.Adj u v)) :
    SameFiber ({j, k} : Finset (Fin n)) G.val H.val ↔
      ∀ w, w ∉ ({i, j, k} : Finset (Fin n)) →
        (G.val.Adj i w ↔ H.val.Adj i w) := by
  classical
  rw [sameFiber_pair_iff_outside G H j k hjk]
  constructor
  · intro h w hw
    have hi : i ∉ ({j, k} : Finset (Fin n)) := by simp [hij, hik]
    have hw' : w ∉ ({j, k} : Finset (Fin n)) := by
      intro hmem
      exact hw (Finset.mem_insert_of_mem hmem)
    exact h i hi w hw'
  · intro hrow u hu v hv
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hu hv
    by_cases hui : u = i
    · subst u
      by_cases hvi : v = i
      · subst v
        simp
      · exact hrow v (by simp [hvi, hv.1, hv.2])
    · by_cases hvi : v = i
      · subst v
        have h := hrow u (by simp [hui, hu.1, hu.2])
        exact ⟨fun hG => (h.mp hG.symm).symm,
          fun hH => (h.mpr hH.symm).symm⟩
      · exact hout u (by simp [hui, hu.1, hu.2]) v (by simp [hvi, hv.1, hv.2])

def tripleRowStates {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i j k : Fin n) : Finset (GraphState n d) :=
  (allGraphStates n d).filter (fun H =>
    (∀ u, u ∉ ({i, j, k} : Finset (Fin n)) →
      ∀ v, v ∉ ({i, j, k} : Finset (Fin n)) →
        (G.val.Adj u v ↔ H.val.Adj u v)) ∧
    (∀ w, w ∉ ({i, j, k} : Finset (Fin n)) →
      (G.val.Adj i w ↔ H.val.Adj i w)))

theorem fiberStates_pair_eq_tripleRowStates {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    fiberStates ({j, k} : Finset (Fin n)) G = tripleRowStates G i j k := by
  classical
  ext H
  simp only [mem_fiberStates, tripleRowStates,
    Finset.mem_filter, allGraphStates, Finset.mem_univ, true_and]
  constructor
  · intro h
    constructor
    · intro u hu v hv
      exact h.1 u (fun hm => hu (Finset.mem_insert_of_mem hm))
        v (fun hm => hv (Finset.mem_insert_of_mem hm))
    · intro w hw
      exact h.1 i (by simp [hij, hik]) w
        (fun hm => hw (Finset.mem_insert_of_mem hm))
  · rintro ⟨hout, hrow⟩
    exact (sameFiber_pair_iff_exterior_row_of_outside G H i j k hij hik hjk hout).mpr hrow

theorem expectation_pair_eq_triple_row_average {n : ℕ} {d : Fin n → ℕ}
    (f : StateSpace n d) (G : GraphState n d) (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    expectation n d ({j, k} : Finset (Fin n)) f G =
      (∑ H ∈ tripleRowStates G i j k, f H) / (tripleRowStates G i j k).card := by
  rw [expectation_eq_average, fiberStates_pair_eq_tripleRowStates G i j k hij hik hjk]

end Problem315.PairResampling

end

end OAI
