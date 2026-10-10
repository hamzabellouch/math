import OAI.Combinatorics.Ramsey.CycleClique.Construction.FourCycleClassCounts

namespace OAI

/-! Manuscript Proposition `small:cases`, the four-cycle case. -/

namespace CycleClique.Construction
theorem no_expanded_fourCycle_counterexample {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {a : ℕ} (ha : 2 ≤ a) (hak : a ≤ 3)
    (hcard : Fintype.card V = 3 * a + 1) (hI : IndependenceBound G a)
    (hcycle : ¬ HasCycle G 4)
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      3 * I.card + 1 ≤ (closedNeighborhood G I).card) : False := by
  classical
  obtain ⟨hlo, hhi⟩ := triangle_clique_bounds (by omega) ha hak hcard hI hcycle
  have hω : G.cliqueNum = 3 := by omega
  obtain ⟨Q, hQ⟩ := G.exists_isNClique_cliqueNum
  have hQcard : Q.card = 3 := hQ.card_eq.trans hω
  let e : Fin 3 ≃ Q := (Finset.equivFinOfCardEq hQcard).symm
  let q : Fin 3 → V := fun i => (e i).val
  have hq : Function.Injective q := Subtype.val_injective.comp e.injective
  have hqQ : ∀ i, q i ∈ Q := fun i => (e i).property
  have hqcover : ∀ x ∈ Q, ∃ i, q i = x := by
    intro x hx
    refine ⟨e.symm ⟨x, hx⟩, ?_⟩
    exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)
  let U := fun i => exteriorNeighbors G Q (q i)
  have hdis : ∀ i j, i ≠ j → Disjoint (U i) (U j) := by
    intro i j hij
    exact fourCycle_triangle_exterior_disjoint hQ.isClique hQcard hcycle (hqQ i) (hqQ j)
      (fun he => hij (hq he))
  have hanti : ∀ i j, i ≠ j → ∀ x ∈ U i, ∀ y ∈ U j, ¬ G.Adj x y := by
    intro i j hij x hx y hy
    exact fourCycle_triangle_exterior_anticomplete hQ.isClique hcycle (hqQ i) (hqQ j)
      (fun he => hij (hq he)) hx hy
  have hU : ∀ i, (U i).Nonempty := by
    intro i
    have hsingleton := hexpand {q i} (by simp) (by simp)
    simp only [Finset.card_singleton, Nat.mul_one] at hsingleton
    have h := exteriorNeighbors_card_lower (hqQ i) hsingleton
    rw [hQcard] at h
    have hpos : 0 < (exteriorNeighbors G Q (q i)).card := by omega
    exact Finset.card_pos.mp hpos
  obtain ⟨ha3, hUclique⟩ := separated_three_cliques hI hak U hU hdis hanti
  have hI3 : IndependenceBound G 3 := by simpa only [ha3] using hI
  have hmax : ∀ i, (U i).card ≤ 2 := by
    intro i
    have hqin : q i ∉ U i := by
      intro h
      exact (mem_exteriorNeighbors.mp h).2 (hqQ i)
    have hjoin : G.IsClique ((insert (q i) (U i) : Finset V) : Set V) := by
      rw [Finset.coe_insert]
      exact (hUclique i).insert (fun u hu _ => (mem_exteriorNeighbors.mp hu).1)
    have hbound := hjoin.card_le_cliqueNum
    rw [Finset.card_insert_of_notMem hqin, hω] at hbound
    omega
  let X := Finset.univ.biUnion U
  have hXcard : X.card = ∑ i, (U i).card :=
    Finset.card_biUnion (fun i _ j _ hij => hdis i j hij)
  have hQX : Disjoint Q X := by
    apply Finset.disjoint_left.mpr
    intro x hx hxX
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hxX
    exact (mem_exteriorNeighbors.mp hi).2 hx
  let W := (Finset.univ : Finset V) \ (Q ∪ X)
  have hcount : W.card + (3 + ∑ i, (U i).card) = 10 := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (Q ∪ X))
    rw [Finset.card_union_of_disjoint hQX, hQcard, hXcard, Finset.card_univ, hcard, ha3] at h
    exact h
  have hsum : (∑ i, (U i).card) ≤ 6 := by
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 3)))
      (f := fun i => (U i).card) (g := fun _ => 2) (fun i _ => hmax i)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using h
  have hW : W.Nonempty := Finset.card_pos.mp (by omega)
  have hwQ : ∀ w ∈ W, w ∉ Q := by
    intro w hw
    exact fun h => (Finset.mem_sdiff.mp hw).2 (Finset.mem_union_left _ h)
  have hwmiss : ∀ w ∈ W, ∀ x ∈ Q, ¬ G.Adj w x := by
    intro w hw x hx hadj
    obtain ⟨i, rfl⟩ := hqcover x hx
    have hwU : w ∈ U i := mem_exteriorNeighbors.mpr ⟨hadj.symm, hwQ w hw⟩
    exact (Finset.mem_sdiff.mp hw).2 (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hwU⟩))
  have htotal := fourCycle_exterior_residual_total hcycle q U hU hmax
    (fun _ _ hu => (mem_exteriorNeighbors.mp hu).1) hdis W hW
    (fun w hw i => ne_of_mem_of_not_mem (hqQ i) (hwQ w hw) |>.symm) (by
      intro w hw
      exact fourCycle_residual_sees_two hQ.isClique hQcard hcycle hI3 q hq hqQ
        (hwQ w hw) (hwmiss w hw))
  omega

end CycleClique.Construction

end OAI
