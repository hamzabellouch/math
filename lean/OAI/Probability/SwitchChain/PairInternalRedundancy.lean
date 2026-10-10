import OAI.Probability.SwitchChain.PairFiberRedundancy

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.PairResampling
attribute [local instance] Classical.propDecidable

theorem pair_degree_sum {n : ℕ} (G : SimpleGraph (Fin n)) (i j : Fin n)
    (hij : i ≠ j) :
    graphDegree G i + graphDegree G j =
      2 * (if G.Adj i j then 1 else 0) +
        ∑ w ∈ Finset.univ \ ({i, j} : Finset (Fin n)),
          (({i, j} : Finset (Fin n)).filter (G.Adj w)).card := by
  classical
  let A : Finset (Fin n) := {i, j}
  let O : Finset (Fin n) := Finset.univ \ A
  have hcross (v : Fin n) :
      ((Finset.univ.filter (G.Adj v)).filter (fun w => w ∉ A)).card =
        ∑ w ∈ O, if G.Adj v w then 1 else 0 := by
    have hs : ((Finset.univ.filter (G.Adj v)).filter (fun w => w ∉ A)) =
        O.filter (G.Adj v) := by
      ext w
      simp [O, and_comm]
    rw [hs, Finset.card_eq_sum_ones, Finset.sum_filter]
  have hpair (w : Fin n) : (A.filter (G.Adj w)).card =
      (if G.Adj w i then 1 else 0) + (if G.Adj w j then 1 else 0) := by
    by_cases hi : G.Adj w i <;> by_cases hj : G.Adj w j <;>
      simp [A, Finset.filter_insert, Finset.filter_singleton, hi, hj, hij]
  have hselfi : (A.filter (G.Adj i)).card = (if G.Adj i j then 1 else 0) := by
    rw [hpair]
    simp
  have hselfj : (A.filter (G.Adj j)).card = (if G.Adj i j then 1 else 0) := by
    rw [hpair]
    simp [G.adj_comm]
  rw [degree_eq_inside_add_outside G A i, degree_eq_inside_add_outside G A j,
    hselfi, hselfj, hcross, hcross]
  change _ = 2 * (if G.Adj i j then 1 else 0) + ∑ w ∈ O, (A.filter (G.Adj w)).card
  simp_rw [hpair, G.adj_comm _ i, G.adj_comm _ j]
  rw [Finset.sum_add_distrib]
  omega

theorem pair_internal_edge_of_outside {n : ℕ} {d : Fin n → ℕ}
    (G H : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (hout : ∀ u, u ∉ ({i, j} : Finset (Fin n)) →
      ∀ v, v ∉ ({i, j} : Finset (Fin n)) → (G.val.Adj u v ↔ H.val.Adj u v)) :
    G.val.Adj i j ↔ H.val.Adj i j := by
  classical
  have hcount := inside_count_eq_of_degrees_outside ({i, j} : Finset (Fin n))
    (fun w => (G.property w).trans (H.property w).symm) hout
  have hs : (∑ w ∈ Finset.univ \ ({i, j} : Finset (Fin n)),
      (({i, j} : Finset (Fin n)).filter (G.val.Adj w)).card) =
      ∑ w ∈ Finset.univ \ ({i, j} : Finset (Fin n)),
        (({i, j} : Finset (Fin n)).filter (H.val.Adj w)).card := by
    apply Finset.sum_congr rfl
    intro w hw
    exact hcount w (Finset.mem_sdiff.mp hw).2
  have hd : graphDegree G.val i + graphDegree G.val j =
      graphDegree H.val i + graphDegree H.val j := by
    rw [G.property i, G.property j, H.property i, H.property j]
  rw [pair_degree_sum G.val i j hij, pair_degree_sum H.val i j hij, hs] at hd
  by_cases hg : G.val.Adj i j <;> by_cases hh : H.val.Adj i j <;> simp_all

theorem sameFiber_pair_iff_outside {n : ℕ} {d : Fin n → ℕ}
    (G H : GraphState n d) (i j : Fin n) (hij : i ≠ j) :
    SameFiber ({i, j} : Finset (Fin n)) G.val H.val ↔
      ∀ u, u ∉ ({i, j} : Finset (Fin n)) →
      ∀ v, v ∉ ({i, j} : Finset (Fin n)) → (G.val.Adj u v ↔ H.val.Adj u v) := by
  constructor
  · exact fun h => h.1
  · intro hout
    apply (sameFiber_iff_outside_inside _ G H).mpr
    refine ⟨hout, ?_⟩
    have hop := pair_internal_edge_of_outside G H i j hij hout
    intro u hu v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · simp
    · exact hop
    · exact ⟨fun hG => (hop.mp hG.symm).symm,
        fun hH => (hop.mpr hH.symm).symm⟩
    · simp

theorem sameFiber_iff_outside_of_card_two {n : ℕ} {d : Fin n → ℕ}
    (a : Finset (Fin n)) (ha : a.card = 2) (G H : GraphState n d) :
    SameFiber a G.val H.val ↔
      ∀ u, u ∉ a → ∀ v, v ∉ a → (G.val.Adj u v ↔ H.val.Adj u v) := by
  obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp ha
  exact sameFiber_pair_iff_outside G H i j hij

theorem mem_fiberSpace_iff_outside_of_card_two {n : ℕ} {d : Fin n → ℕ}
    (a : Finset (Fin n)) (ha : a.card = 2) (f : StateSpace n d) :
    f ∈ fiberSpace n d a ↔
      ∀ G H : GraphState n d,
        (∀ u, u ∉ a → ∀ v, v ∉ a → (G.val.Adj u v ↔ H.val.Adj u v)) →
          f G = f H := by
  constructor
  · intro hf G H h
    exact hf G H ((sameFiber_iff_outside_of_card_two a ha G H).mpr h)
  · intro hf G H h
    exact hf G H ((sameFiber_iff_outside_of_card_two a ha G H).mp h)

end Problem315.PairResampling

end

end OAI
