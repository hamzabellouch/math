import OAI.Combinatorics.Ramsey.CycleClique.Construction.FiveCycleExteriorSix

namespace OAI

/-! Manuscript Proposition `small:cases`, the five-cycle case. -/

namespace CycleClique.Construction
theorem no_expanded_fiveCycle_counterexample {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {a : ℕ} (ha : 2 ≤ a) (hak : a ≤ 4)
    (hcard : Fintype.card V = 4 * a + 1) (hI : IndependenceBound G a)
    (hcycle : ¬ HasCycle G 5)
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      4 * I.card + 1 ≤ (closedNeighborhood G I).card) : False := by
  classical
  have horder : Fintype.card V ≤ 17 := by omega
  have hsingleton : ∀ v, 5 ≤ (closedNeighborhood G {v}).card := by
    intro v
    simpa only [Finset.card_singleton, Nat.mul_one] using hexpand {v} (by simp) (by simp)
  obtain ⟨htriangle, hupper⟩ := triangle_clique_bounds (by omega) ha hak hcard hI hcycle
  have hω : G.cliqueNum ≤ 3 := by
    by_contra hn
    have hω4 : G.cliqueNum = 4 := by omega
    obtain ⟨Q, hQ⟩ := G.exists_isNClique_cliqueNum
    exact fiveCycle_fourClique_impossible hcycle horder hsingleton hQ.isClique (hQ.card_eq.trans hω4)
  have hω3 : G.cliqueNum = 3 := by omega
  obtain ⟨Q, hQ⟩ := G.exists_isNClique_cliqueNum
  have hQcard : Q.card = 3 := hQ.card_eq.trans hω3
  let e : Fin 3 ≃ Q := (Finset.equivFinOfCardEq hQcard).symm
  let q : Fin 3 → V := fun i => (e i).val
  have hq : Function.Injective q := Subtype.val_injective.comp e.injective
  have hqQ : ∀ i, q i ∈ Q := fun i => (e i).property
  have hdis : ∀ T : Finset V, G.IsClique (T : Set V) → T.card = 3 →
      ∀ x ∈ T, ∀ y ∈ T, x ≠ y → Disjoint (exteriorNeighbors G T x) (exteriorNeighbors G T y) := by
    intro T hT hTcard x hx y hy hxy
    exact fiveCycle_triangle_exterior_disjoint hT hTcard hcycle hω horder hexpand hx hy hxy
  have hQdis := hdis Q hQ.isClique hQcard
  have hstructure := fiveCycle_disjoint_triangle_structure hQ.isClique hQcard hcycle hω horder hexpand hQdis q hq hqQ
  let U := fun i => exteriorNeighbors G Q (q i)
  let C := fun i => exteriorClosedNeighborhood G Q (U i)
  have hCdis : ∀ i j, i ≠ j → Disjoint (C i) (C j) := by
    intro i j hij
    exact fiveCycle_exterior_closed_disjoint hQ.isClique (by omega) hcycle (hqQ i) (hqQ j)
      (fun h => hij (hq h)) (fun _ h => h) (fun _ h => h)
      (hQdis _ (hqQ i) _ (hqQ j) (fun h => hij (hq h)))
  have hCsix : ∀ i, 6 ≤ (C i).card := by
    intro i
    obtain ⟨hUcard, hUclique⟩ := hstructure i
    exact fiveCycle_exterior_closed_six (fun _ h => h) hUclique hUcard
      (fun u hu x hx hux => exterior_unique_clique_neighbor hQdis (hqQ i) hu hx hux) hsingleton hdis
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 3)))
    (f := fun _ => 6) (g := fun i => (C i).card) (fun i _ => hCsix i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  have hbound := exterior_disjoint_sum_bound Finset.univ U (fun i _ j _ hij => hCdis i j hij)
  rw [hQcard] at hbound
  change 3 + ∑ i : Fin 3, (C i).card ≤ Fintype.card V at hbound
  omega

end CycleClique.Construction

end OAI
