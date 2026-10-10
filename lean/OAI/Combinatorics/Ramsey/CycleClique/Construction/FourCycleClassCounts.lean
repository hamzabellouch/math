import OAI.Combinatorics.Ramsey.CycleClique.Construction.FourCycleResidual

namespace OAI

/-! The last three-class pigeonhole step in the four-cycle exclusion. -/

namespace CycleClique.Construction
private theorem fin_three_two_of_not {P : Fin 3 → Prop}
    (hex : ∃ a b, a ≠ b ∧ P a ∧ P b) {i j : Fin 3} (hi : ¬ P i) (hji : j ≠ i) : P j := by
  obtain ⟨a, b, hab, ha, hb⟩ := hex
  by_contra hj
  have hai : a.val ≠ i.val := fun h => hi (Fin.ext h ▸ ha)
  have haj : a.val ≠ j.val := fun h => hj (Fin.ext h ▸ ha)
  have hbi : b.val ≠ i.val := fun h => hi (Fin.ext h ▸ hb)
  have hbj : b.val ≠ j.val := fun h => hj (Fin.ext h ▸ hb)
  have hab' : a.val ≠ b.val := fun h => hab (Fin.ext h)
  have hij' : j.val ≠ i.val := fun h => hji (Fin.ext h)
  have := a.isLt
  have := b.isLt
  have := i.isLt
  have := j.isLt
  omega

private theorem three_sizes_sum_le_four (c : Fin 3 → ℕ) (hmax : ∀ i, c i ≤ 2)
    {j h : Fin 3} (hjh : j ≠ h) (hj : c j ≤ 1) (hh : c h ≤ 1) :
    ∑ i, c i ≤ 4 := by
  classical
  have hbonus : (∑ i : Fin 3, if i = j ∨ i = h then 1 else 0) = 2 := by
    have hfilter : (Finset.univ : Finset (Fin 3)).filter (fun i => i = j ∨ i = h) = {j, h} := by
      ext i
      simp
    simp only [Finset.sum_boole, hfilter, Finset.card_pair hjh]
    norm_num
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 3))) (f := fun i =>
    c i + if i = j ∨ i = h then 1 else 0) (g := fun _ => 2) (by
      intro i _
      by_cases hi : i = j ∨ i = h
      · rcases hi with rfl | rfl <;> simp only [true_or, or_true, ite_true] <;> omega
      · simpa only [ite_eq_right hi, Nat.add_zero] using hmax i)
  rw [Finset.sum_add_distrib, hbonus] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  omega

theorem fourCycle_exterior_residual_total {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hcycle : ¬ HasCycle G 4)
    (q : Fin 3 → V) (U : Fin 3 → Finset V)
    (hU : ∀ i, (U i).Nonempty) (hmax : ∀ i, (U i).card ≤ 2)
    (hUi : ∀ i u, u ∈ U i → G.Adj (q i) u)
    (hdis : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (W : Finset V) (hW : W.Nonempty) (hwq : ∀ w ∈ W, ∀ i, w ≠ q i)
    (hsees : ∀ w ∈ W, ∃ i j : Fin 3, i ≠ j ∧
      (∀ u ∈ U i, G.Adj w u) ∧ (∀ u ∈ U j, G.Adj w u)) :
    (∑ i, (U i).card) + W.card ≤ 6 := by
  classical
  choose f hf using hU
  have hfinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    exact Finset.disjoint_left.mp (hdis i j hne) (hf i) (hij ▸ hf j)
  have hWthree : W.card ≤ 3 := fourCycle_three_representatives_bound hcycle f hfinj W (by
    intro w hw
    obtain ⟨i, j, hij, hi, hj⟩ := hsees w hw
    exact ⟨i, j, hij, hi _ (hf i), hj _ (hf j)⟩)
  have hfullcard : ∀ w ∈ W, ∀ i, (∀ u ∈ U i, G.Adj w u) → (U i).card ≤ 1 := by
    intro w hw i hfull
    exact fourCycle_common_neighbors_card hcycle (hwq w hw i).symm (U i)
      (fun u hu => ⟨hUi i u hu, hfull u hu⟩)
  by_cases htwo : ∃ i, 2 ≤ (U i).card
  · obtain ⟨i, hi⟩ := htwo
    have hnotfull : ∀ w ∈ W, ¬ ∀ u ∈ U i, G.Adj w u := by
      intro w hw hfull
      have := hfullcard w hw i hfull
      omega
    have hotherfull : ∀ w ∈ W, ∀ j, j ≠ i → ∀ u ∈ U j, G.Adj w u := by
      intro w hw j hji
      exact fin_three_two_of_not (hsees w hw) (hnotfull w hw) hji
    obtain ⟨j, _, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (show ({i} : Finset (Fin 3)).card < (Finset.univ : Finset (Fin 3)).card by simp)
    have hji : j ≠ i := by simpa only [Finset.mem_singleton] using hj
    obtain ⟨h, hhj, hhi⟩ := exists_third_fin_three hji
    have hWone : W.card ≤ 1 := fourCycle_common_neighbors_card hcycle
      (fun he => hhj (hfinj he).symm) W (by
        intro w hw
        exact ⟨(hotherfull w hw j hji _ (hf j)).symm,
          (hotherfull w hw h hhi _ (hf h)).symm⟩)
    obtain ⟨w, hw⟩ := hW
    obtain ⟨j', h', hjh, hjfull, hhfull⟩ := hsees w hw
    have hsum := three_sizes_sum_le_four (fun i => (U i).card) hmax hjh
      (hfullcard w hw j' hjfull) (hfullcard w hw h' hhfull)
    omega
  · have hone : ∀ i, (U i).card ≤ 1 := by intro i; by_contra hn; exact htwo ⟨i, by omega⟩
    have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 3)))
      (f := fun i => (U i).card) (g := fun _ => 1) (fun i _ => hone i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
    omega

end CycleClique.Construction

end OAI
