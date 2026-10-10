import OAI.Combinatorics.SecondNeighborhood.MatchingExchange

namespace OAI

namespace SeymourSecondNeighborhood.Bipartite

variable {L R : Type*} [Fintype L] [Fintype R]
    [DecidableEq L] [DecidableEq R]
    {E : L → R → Prop}

omit [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R] in
private theorem augmented_matching_subset {M N : Finset (L × R)}
    (hM : IsMatching E M) (hNM : N ⊆ M) : IsMatching E N := by
  exact ⟨fun e he => hM.1 e (hNM he),
    fun _ he _ hf h => hM.2.1 (hNM he) (hNM hf) h,
    fun _ he _ hf h => hM.2.2 (hNM he) (hNM hf) h⟩

theorem isMaximumMatching_rightBlock_of_minimum_crossing
    (P : L → Prop) (Q : R → Prop) [DecidablePred P] [DecidablePred Q]
    (hblock : ∀ a b, E a b → Q b → P a)
    {M : Finset (L × R)} (hM : IsMaximumMatching E M)
    (hmin : ∀ N : Finset (L × R), IsMaximumMatching E N →
      (M.filter (fun e => P e.1 ∧ ¬Q e.2)).card ≤
        (N.filter (fun e => P e.1 ∧ ¬Q e.2)).card) :
    IsMaximumMatching (fun a b => E a b ∧ Q b)
      (M.filter (fun e => Q e.2)) := by
  classical
  let α := M.filter (fun e => Q e.2)
  let T := M \ α
  have hαM : α ⊆ M := Finset.filter_subset _ _
  have hα : IsMatching (fun a b => E a b ∧ Q b) α := by
    refine ⟨?_, (augmented_matching_subset hM.1 hαM).2⟩
    intro e he
    exact ⟨hM.1.1 e (hαM he), (Finset.mem_filter.mp he).2⟩
  refine ⟨hα, ?_⟩
  intro N hN
  by_contra hlarge
  have hlarge' : α.card < N.card := Nat.lt_of_not_ge hlarge
  obtain ⟨B, hB, hBcard, hBleft⟩ :=
    exists_matching_one_larger_saturating_left hα hN hlarge'
  have hBE : IsMatching E B :=
    ⟨fun e he => (hB.1 e he).1, hB.2⟩
  have hT : IsMatching E T :=
    augmented_matching_subset hM.1 Finset.sdiff_subset
  have hTnotQ : ∀ e ∈ T, ¬Q e.2 := by
    intro e he hQ
    exact (Finset.mem_sdiff.mp he).2
      (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp he).1, hQ⟩)
  let D := T.filter (fun e => e.1 ∈ B.image Prod.fst)
  let U := T \ D
  let M' := U ∪ B
  have hDT : D ⊆ T := Finset.filter_subset _ _
  have hUM : U ⊆ M := fun e he =>
    (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp he).1).1
  have hDcross : ∀ e ∈ D, P e.1 ∧ ¬Q e.2 := by
    intro e he
    have heT := hDT he
    obtain ⟨b, hbB, hb⟩ := Finset.mem_image.mp (Finset.mem_filter.mp he).2
    refine ⟨?_, hTnotQ e heT⟩
    have hbP := hblock b.1 b.2 (hB.1 b hbB).1 (hB.1 b hbB).2
    simpa only [hb] using hbP
  have hDleft : D.image Prod.fst ⊆ B.image Prod.fst \ α.image Prod.fst := by
    intro a ha
    obtain ⟨e, heD, rfl⟩ := Finset.mem_image.mp ha
    refine Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp heD).2, ?_⟩
    intro heα
    obtain ⟨f, hfα, hfe⟩ := Finset.mem_image.mp heα
    have heM : e ∈ M := (Finset.mem_sdiff.mp (hDT heD)).1
    have hfe' : f = e := hM.1.2.1 (hαM hfα) heM hfe
    exact (Finset.mem_sdiff.mp (hDT heD)).2 (hfe' ▸ hfα)
  have hDcard : D.card ≤ 1 := by
    have hDinj : Set.InjOn Prod.fst (↑D : Set (L × R)) :=
      fun _ he _ hf h => hT.2.1 (hDT he) (hDT hf) h
    have hc := Finset.card_le_card hDleft
    rw [Finset.card_image_of_injOn hDinj,
      Finset.card_sdiff_of_subset hBleft,
      Finset.card_image_of_injOn hB.2.1,
      Finset.card_image_of_injOn hα.2.1] at hc
    omega
  have hUBleft : ∀ u ∈ U, ∀ b ∈ B, u.1 ≠ b.1 := by
    intro u hu b hb hub
    have huT : u ∈ T := (Finset.mem_sdiff.mp hu).1
    have huD : u ∈ D := Finset.mem_filter.mpr
      ⟨huT, Finset.mem_image.mpr ⟨b, hb, hub.symm⟩⟩
    exact (Finset.mem_sdiff.mp hu).2 huD
  have hUBright : ∀ u ∈ U, ∀ b ∈ B, u.2 ≠ b.2 := by
    intro u hu b hb hub
    apply hTnotQ u (Finset.mem_sdiff.mp hu).1
    rw [hub]
    exact (hB.1 b hb).2
  have hU : IsMatching E U := augmented_matching_subset hM.1 hUM
  have hM'match : IsMatching E M' := by
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      rcases Finset.mem_union.mp he with he | he
      · exact hU.1 e he
      · exact hBE.1 e he
    · intro e he f hf hef
      rcases Finset.mem_union.mp he with he | he
      · rcases Finset.mem_union.mp hf with hf | hf
        · exact hU.2.1 he hf hef
        · exact False.elim (hUBleft e he f hf hef)
      · rcases Finset.mem_union.mp hf with hf | hf
        · exact False.elim (hUBleft f hf e he hef.symm)
        · exact hBE.2.1 he hf hef
    · intro e he f hf hef
      rcases Finset.mem_union.mp he with he | he
      · rcases Finset.mem_union.mp hf with hf | hf
        · exact hU.2.2 he hf hef
        · exact False.elim (hUBright e he f hf hef)
      · rcases Finset.mem_union.mp hf with hf | hf
        · exact False.elim (hUBright f hf e he hef.symm)
        · exact hBE.2.2 he hf hef
  have hUBdisjoint : Disjoint U B := by
    apply Finset.disjoint_left.mpr
    intro e heU heB
    exact hUBleft e heU e heB rfl
  have hM'card : M'.card + D.card = M.card + 1 := by
    have hpart := Finset.card_sdiff_add_card_eq_card hαM
    have hpart' := Finset.card_sdiff_add_card_eq_card hDT
    have hunion := Finset.card_union_of_disjoint hUBdisjoint
    change M'.card = U.card + B.card at hunion
    change T.card + α.card = M.card at hpart
    change U.card + D.card = T.card at hpart'
    omega
  have hM'le : M'.card ≤ M.card := hM.2 M' hM'match
  have hDeq : D.card = 1 := by omega
  have hM'eq : M'.card = M.card := by omega
  have hM'max : IsMaximumMatching E M' := by
    refine ⟨hM'match, ?_⟩
    intro N' hN'
    rw [hM'eq]
    exact hM.2 N' hN'
  let C := M.filter (fun e => P e.1 ∧ ¬Q e.2)
  have hDC : D ⊆ C := by
    intro e he
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_sdiff.mp (hDT he)).1, hDcross e he⟩
  have hcost : M'.filter (fun e => P e.1 ∧ ¬Q e.2) = C \ D := by
    ext e
    constructor
    · intro he
      obtain ⟨he, hPe, hnQe⟩ := Finset.mem_filter.mp he
      rcases Finset.mem_union.mp he with heU | heB
      · exact Finset.mem_sdiff.mpr
          ⟨Finset.mem_filter.mpr ⟨hUM heU, hPe, hnQe⟩,
            (Finset.mem_sdiff.mp heU).2⟩
      · exact False.elim (hnQe (hB.1 e heB).2)
    · intro he
      obtain ⟨heC, heD⟩ := Finset.mem_sdiff.mp he
      obtain ⟨heM, hPe, hnQe⟩ := Finset.mem_filter.mp heC
      have heT : e ∈ T := Finset.mem_sdiff.mpr
        ⟨heM, fun heα => hnQe (Finset.mem_filter.mp heα).2⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨heT, heD⟩)), hPe, hnQe⟩
  have hmin' := hmin M' hM'max
  rw [hcost] at hmin'
  have hpart := Finset.card_sdiff_add_card_eq_card hDC
  change C.card ≤ (C \ D).card at hmin'
  omega

def swapMatching (M : Finset (L × R)) : Finset (R × L) := M.image Prod.swap

omit [Fintype L] [Fintype R] in
@[simp] theorem mem_swapMatching {M : Finset (L × R)} {e : R × L} :
    e ∈ swapMatching M ↔ e.swap ∈ M := by
  constructor
  · intro he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    simpa using hf
  · intro he
    exact Finset.mem_image.mpr ⟨e.swap, he, Prod.swap_swap e⟩

omit [Fintype L] [Fintype R] in
@[simp] theorem card_swapMatching (M : Finset (L × R)) :
    (swapMatching M).card = M.card := by
  exact Finset.card_image_of_injective _ Prod.swap_injective

omit [Fintype L] [Fintype R] in
@[simp] theorem swapMatching_swapMatching (M : Finset (L × R)) :
    swapMatching (swapMatching M) = M := by
  ext e
  simp

omit [Fintype L] [Fintype R] in
theorem filter_swapMatching (M : Finset (L × R))
    (p : R × L → Prop) [DecidablePred p] :
    (swapMatching M).filter p = swapMatching (M.filter (fun e => p e.swap)) := by
  ext e
  simp

omit [Fintype L] [Fintype R] in
@[simp] theorem card_filter_swapMatching (M : Finset (L × R))
    (p : R × L → Prop) [DecidablePred p] :
    ((swapMatching M).filter p).card = (M.filter (fun e => p e.swap)).card := by
  rw [filter_swapMatching, card_swapMatching]

omit [Fintype L] [Fintype R] in
theorem IsMatching.swap {M : Finset (L × R)} (hM : IsMatching E M) :
    IsMatching (fun b a => E a b) (swapMatching M) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    exact hM.1 e.swap (mem_swapMatching.mp he)
  · intro e he f hf hef
    apply Prod.swap_injective
    exact hM.2.2 (mem_swapMatching.mp he) (mem_swapMatching.mp hf) hef
  · intro e he f hf hef
    apply Prod.swap_injective
    exact hM.2.1 (mem_swapMatching.mp he) (mem_swapMatching.mp hf) hef

omit [Fintype L] [Fintype R] in
theorem IsMaximumMatching.swap {M : Finset (L × R)}
    (hM : IsMaximumMatching E M) :
    IsMaximumMatching (fun b a => E a b) (swapMatching M) := by
  refine ⟨hM.1.swap, ?_⟩
  intro N hN
  have hcard := hM.2 (swapMatching N) hN.swap
  simpa using hcard

theorem isMaximumMatching_leftBlock_of_minimum_crossing
    (P : L → Prop) (Q : R → Prop) [DecidablePred P] [DecidablePred Q]
    (hblock : ∀ a b, E a b → Q b → P a)
    {M : Finset (L × R)} (hM : IsMaximumMatching E M)
    (hmin : ∀ N : Finset (L × R), IsMaximumMatching E N →
      (M.filter (fun e => P e.1 ∧ ¬Q e.2)).card ≤
        (N.filter (fun e => P e.1 ∧ ¬Q e.2)).card) :
    IsMaximumMatching (fun a b => E a b ∧ ¬P a)
      (M.filter (fun e => ¬P e.1)) := by
  classical
  have hblock' : ∀ b a, E a b → ¬P a → ¬Q b := by
    intro b a he hnP hQ
    exact hnP (hblock a b he hQ)
  have hmin' : ∀ N : Finset (R × L),
      IsMaximumMatching (fun b a => E a b) N →
      ((swapMatching M).filter (fun e => ¬Q e.1 ∧ ¬¬P e.2)).card ≤
        (N.filter (fun e => ¬Q e.1 ∧ ¬¬P e.2)).card := by
    intro N hN
    have h := hmin (swapMatching N) hN.swap
    simpa [and_comm] using h
  have hright := isMaximumMatching_rightBlock_of_minimum_crossing
    (fun b => ¬Q b) (fun a => ¬P a) hblock' hM.swap hmin'
  have hleft := hright.swap
  simpa only [filter_swapMatching, swapMatching_swapMatching,
    Prod.snd_swap] using hleft

theorem exists_maximum_matching_with_maximum_blocks
    (P : L → Prop) (Q : R → Prop) [DecidablePred P] [DecidablePred Q]
    (hblock : ∀ a b, E a b → Q b → P a) :
    ∃ M : Finset (L × R), IsMaximumMatching E M ∧
      IsMaximumMatching (fun a b => E a b ∧ Q b)
        (M.filter (fun e => Q e.2)) ∧
      IsMaximumMatching (fun a b => E a b ∧ ¬P a)
        (M.filter (fun e => ¬P e.1)) := by
  classical
  obtain ⟨M, hM, hmin⟩ := exists_maximum_matching_min_cost E
    (fun N => (N.filter (fun e => P e.1 ∧ ¬Q e.2)).card)
  have hmin' : ∀ N : Finset (L × R), IsMaximumMatching E N →
      (M.filter (fun e => P e.1 ∧ ¬Q e.2)).card ≤
        (N.filter (fun e => P e.1 ∧ ¬Q e.2)).card := by
    intro N hN
    exact hmin N hN.1 (Nat.le_antisymm (hM.2 N hN.1) (hN.2 M hM.1))
  exact ⟨M, hM,
    isMaximumMatching_rightBlock_of_minimum_crossing P Q hblock hM hmin',
    isMaximumMatching_leftBlock_of_minimum_crossing P Q hblock hM hmin'⟩

end SeymourSecondNeighborhood.Bipartite

end OAI
