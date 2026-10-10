import OAI.Combinatorics.Ramsey.CycleClique.Construction.Reduction
import OAI.Combinatorics.Ramsey.CycleClique.Construction.Triangle

namespace OAI

/-!
# The initial clique bounds

The triangle bound is manuscript Lemma `clq:triangle`. Its proof below
establishes the elementary triangle Ramsey recurrence directly, without
assuming any cycle–clique Ramsey theorem.
-/

namespace CycleClique.Construction
private theorem cycleNext_ne {m : ℕ} (hm : 2 ≤ m) (i : Fin m) : cycleNext i ≠ i := by
  intro h
  have heq := congrArg Fin.val h
  change (i.val + 1) % m = i.val at heq
  by_cases hi : i.val + 1 < m
  · rw [Nat.mod_eq_of_lt hi] at heq
    omega
  · have hlast : i.val + 1 = m := by omega
    rw [hlast, Nat.mod_self] at heq
    omega

/-- A clique contains a cycle through any specified number of at least
three of its vertices. -/
theorem clique_contains_cycle {V : Type*} {G : SimpleGraph V} {Q : Finset V} {m : ℕ}
    (hm : 3 ≤ m) (hQ : G.IsClique (Q : Set V)) (hcard : m ≤ Q.card) : HasCycle G m := by
  classical
  obtain ⟨S, hSQ, hS⟩ := Finset.exists_subset_card_eq hcard
  let e : Fin m ≃ S := (Finset.equivFinOfCardEq hS).symm
  refine ⟨fun i => (e i).val, Subtype.val_injective.comp e.injective, ?_⟩
  intro i
  apply hQ (hSQ (e i).property) (hSQ (e (cycleNext i)).property)
  intro h
  have heq := e.injective (Subtype.ext h)
  exact cycleNext_ne (by omega) i heq.symm

/-- The elementary triangle Ramsey bound, in doubled form to avoid
division: a triangle-free graph of independence number at most `a`
has at most `a * (a + 3) / 2` vertices. -/
theorem triangle_free_order_bound (a : ℕ) :
    ∀ {V : Type*} [Fintype V] {G : SimpleGraph V},
      IndependenceBound G a → ¬ HasCycle G 3 →
      2 * Fintype.card V ≤ a * (a + 3) := by
  induction a with
  | zero =>
    intro V _ G hI _
    have hempty : IsEmpty V := ⟨fun v => by
      have h := hI {v} (by simp)
      simp at h⟩
    simp
  | succ a ih =>
    intro V _ G hI htriangle
    classical
    by_cases hnonempty : Nonempty V
    · obtain ⟨v⟩ := hnonempty
      have hN : G.IsIndepSet (G.neighborFinset v : Set V) := by
        intro x hx y hy _ hxy
        exact htriangle (hasCycle_three_of_edges ((G.mem_neighborFinset v x).mp hx) hxy
          ((G.mem_neighborFinset v y).mp hy).symm)
      have hdegree := hI (G.neighborFinset v) hN
      have hclosed : closedNeighborhood G {v} = insert v (G.neighborFinset v) := by
        ext w
        simp [mem_closedNeighborhood]
      have hv : v ∉ G.neighborFinset v := by simp
      have hclosedCard : (closedNeighborhood G {v}).card ≤ a + 2 := by
        rw [hclosed, Finset.card_insert_of_notMem hv]
        omega
      let Y : Finset V := Finset.univ \ closedNeighborhood G {v}
      have hY : (Y : Set V) = {w | w ∉ closedNeighborhood G {v}} := by ext w; simp [Y]
      have hIY : IndependenceBound (G.induce (Y : Set V)) a := by
        rw [hY]
        simpa using independent_outside_bound hI (I := {v}) (by simp)
      have htriangleY : ¬ HasCycle (G.induce (Y : Set V)) 3 := by
        intro h
        exact htriangle (h.map Subtype.val Subtype.val_injective (fun h => h))
      have hYbound : 2 * Y.card ≤ a * (a + 3) := by simpa using ih hIY htriangleY
      have hsum : Y.card + (closedNeighborhood G {v}).card = Fintype.card V := by
        simpa [Y] using Finset.card_sdiff_add_card_eq_card
          (Finset.subset_univ (closedNeighborhood G {v}))
      nlinarith
    · have : IsEmpty V := not_nonempty_iff.mp hnonempty
      simp

/-- A cycle-free graph has no clique larger than the forbidden cycle order. -/
theorem cliqueNum_le_of_no_cycle {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} (hk : 2 ≤ k) (hcycle : ¬ HasCycle G (k + 1)) : G.cliqueNum ≤ k := by
  by_contra hn
  obtain ⟨Q, hQ⟩ := G.exists_isNClique_cliqueNum
  have hsize := hQ.card_eq
  apply hcycle
  exact clique_contains_cycle (by omega) hQ.isClique (by omega)

/-- Manuscript Lemma `clq:triangle`, valid before using expansion. -/
theorem triangle_clique_bounds {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k a : ℕ} (hk : 3 ≤ k) (_ha : 2 ≤ a) (hak : a ≤ k)
    (hcard : Fintype.card V = k * a + 1)
    (hI : IndependenceBound G a) (hcycle : ¬ HasCycle G (k + 1)) :
    3 ≤ G.cliqueNum ∧ G.cliqueNum ≤ k := by
  classical
  have htriangle : HasCycle G 3 := by
    by_contra hn
    have hb := triangle_free_order_bound a hI hn
    have hparam : a + 3 ≤ 2 * k := by omega
    rw [hcard] at hb
    nlinarith
  obtain ⟨f, _, he⟩ := htriangle
  have h01 : G.Adj (f 0) (f 1) := by simpa [cycleNext] using he 0
  have h12 : G.Adj (f 1) (f 2) := by simpa [cycleNext] using he 1
  have h20 : G.Adj (f 2) (f 0) := by simpa [cycleNext] using he 2
  have hQ : G.IsNClique 3 {f 0, f 1, f 2} :=
    SimpleGraph.is3Clique_triple_iff.mpr ⟨h01, h20.symm, h12⟩
  refine ⟨?_, cliqueNum_le_of_no_cycle (by omega) hcycle⟩
  simpa [hQ.card_eq] using hQ.isClique.card_le_cliqueNum

/-- For the first five cycle lengths, the triangle already gives the
complete quantitative clique bound of Theorem `clq:bound`. -/
theorem large_clique_small_k {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k a : ℕ} (hk : 3 ≤ k) (hk7 : k ≤ 7) (ha : 2 ≤ a) (hak : a ≤ k)
    (hcard : Fintype.card V = k * a + 1)
    (hI : IndependenceBound G a) (hcycle : ¬ HasCycle G (k + 1)) :
    max 3 (k / 2) ≤ G.cliqueNum ∧ G.cliqueNum ≤ k := by
  obtain ⟨hlo, hhi⟩ := triangle_clique_bounds hk ha hak hcard hI hcycle
  exact ⟨by omega, hhi⟩

end CycleClique.Construction

end OAI
