import OAI.Combinatorics.BinaryEdit.BlockPairCount

namespace OAI

namespace TreeEdit.BinaryLower

noncomputable section

/-- The integer interval hull of the positions bearing one matching label.
The empty fiber has empty span. -/
def matchingSpan {r n : ℕ} {β : Type*} [DecidableEq β] (f : Fin r → Fin n)
    (label : Fin r → β) (b : β) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun p =>
    ∃ i j, label i = b ∧ label j = b ∧ f i ≤ p ∧ p ≤ f j

@[simp] theorem mem_matchingSpan {r n : ℕ} {β : Type*} [DecidableEq β]
    (f : Fin r → Fin n) (label : Fin r → β) (b : β) (p : Fin n) :
    p ∈ matchingSpan f label b ↔
      ∃ i j, label i = b ∧ label j = b ∧ f i ≤ p ∧ p ≤ f j := by
  classical
  simp [matchingSpan]

/-- Each matched position of a fiber belongs to its span. -/
theorem matchingSpan_contains_match {r n : ℕ} {β : Type*} [DecidableEq β]
    (f : Fin r → Fin n) (label : Fin r → β) {b : β} {i : Fin r}
    (hi : label i = b) : f i ∈ matchingSpan f label b :=
  (mem_matchingSpan f label b (f i)).mpr ⟨i, i, hi, hi, le_rfl, le_rfl⟩

/-- An order-convex label fiber contains every matched position in its span. -/
theorem matchingSpan_inter_image {r n : ℕ} {β : Type*} [DecidableEq β]
    (f : Fin r → Fin n) (hf : StrictMono f) (label : Fin r → β)
    (hc : ∀ {i j k}, i ≤ j → j ≤ k → label i = label k → label j = label i)
    (b : β) :
    matchingSpan f label b ∩ Finset.univ.image f =
      (Finset.univ.filter fun i => label i = b).image f := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨hspan, himage⟩ := Finset.mem_inter.mp hp
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp himage
    obtain ⟨i, j, hi, hj, hleft, hright⟩ :=
      (mem_matchingSpan f label b (f k)).mp hspan
    apply Finset.mem_image.mpr
    refine ⟨k, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    exact (hc (hf.le_iff_le.mp hleft) (hf.le_iff_le.mp hright)
      (hi.trans hj.symm)).trans hi
  · intro hp
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hp
    have hlabel := (Finset.mem_filter.mp hk).2
    apply Finset.mem_inter.mpr
    constructor
    · exact (mem_matchingSpan f label b (f k)).mpr
        ⟨k, k, hlabel, hlabel, le_rfl, le_rfl⟩
    · exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩

/-- Distinct order-convex label fibers have disjoint interval hulls. -/
theorem matchingSpan_disjoint {r n : ℕ} {β : Type*} [DecidableEq β]
    (f : Fin r → Fin n) (hf : StrictMono f) (label : Fin r → β)
    (hc : ∀ {i j k}, i ≤ j → j ≤ k → label i = label k → label j = label i)
    {b c : β} (hbc : b ≠ c) :
    Disjoint (matchingSpan f label b) (matchingSpan f label c) := by
  classical
  apply Finset.disjoint_left.mpr
  intro p hp hq
  obtain ⟨i, j, hi, hj, hip, hpj⟩ := (mem_matchingSpan f label b p).mp hp
  obtain ⟨k, l, hk, hl, hkp, hpl⟩ := (mem_matchingSpan f label c p).mp hq
  rcases le_total i k with hik | hki
  · have hkj : k ≤ j := hf.le_iff_le.mp (hkp.trans hpj)
    have heq := hc hik hkj (hi.trans hj.symm)
    exact hbc (hi.symm.trans (heq.symm.trans hk))
  · have hil : i ≤ l := hf.le_iff_le.mp (hip.trans hpl)
    have heq := hc hki hil (hk.trans hl.symm)
    exact hbc (hi.symm.trans (heq.trans hk))

/-- The number of unmatched positions in a span is its length minus the
number of matching entries in the corresponding fiber. -/
theorem matchingSpan_unmatched_card {r n : ℕ} {β : Type*} [DecidableEq β]
    (f : Fin r → Fin n) (hf : StrictMono f) (label : Fin r → β)
    (hc : ∀ {i j k}, i ≤ j → j ≤ k → label i = label k → label j = label i)
    (b : β) :
    (matchingSpan f label b \ Finset.univ.image f).card =
      (matchingSpan f label b).card - (Finset.univ.filter fun i => label i = b).card := by
  classical
  rw [Finset.card_sdiff, Finset.inter_comm, matchingSpan_inter_image f hf label hc]
  rw [Finset.card_image_of_injective _ hf.injective]

/-- All span gaps together use at most the global number of unmatched
positions. This holds for any selected collection of label fibers. -/
theorem matchingSpan_gap_budget {r n : ℕ} {β : Type*} [DecidableEq β]
    (f : Fin r → Fin n) (hf : StrictMono f) (label : Fin r → β)
    (hc : ∀ {i j k}, i ≤ j → j ≤ k → label i = label k → label j = label i)
    (s : Finset β) :
    (∑ b ∈ s, ((matchingSpan f label b).card -
      (Finset.univ.filter fun i => label i = b).card)) ≤ n - r := by
  classical
  let gaps : β → Finset (Fin n) := fun b =>
    matchingSpan f label b \ Finset.univ.image f
  have hdisj : (↑s : Set β).PairwiseDisjoint gaps := by
    intro b hb c hc' hbc
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact (Finset.disjoint_left.mp (matchingSpan_disjoint f hf label hc hbc))
      (Finset.mem_sdiff.mp hp).1 (Finset.mem_sdiff.mp hq).1
  have hsub : s.biUnion gaps ⊆ Finset.univ \ Finset.univ.image f := by
    intro p hp
    obtain ⟨b, hb, hpb⟩ := Finset.mem_biUnion.mp hp
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hpb).2⟩
  calc
    (∑ b ∈ s, ((matchingSpan f label b).card -
        (Finset.univ.filter fun i => label i = b).card)) = ∑ b ∈ s, (gaps b).card := by
      apply Finset.sum_congr rfl
      intro b hb
      exact (matchingSpan_unmatched_card f hf label hc b).symm
    _ = (s.biUnion gaps).card := (Finset.card_biUnion hdisj).symm
    _ ≤ (Finset.univ \ Finset.univ.image f).card := Finset.card_le_card hsub
    _ = n - r := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
      rw [Finset.card_image_of_injective _ hf.injective]
      simp

/-- There cannot be more matching entries in a fiber than positions in its span. -/
theorem matchingSpan_fiber_card_le {r n : ℕ} {β : Type*} [DecidableEq β]
    (f : Fin r → Fin n) (hf : StrictMono f) (label : Fin r → β)
    (hc : ∀ {i j k}, i ≤ j → j ≤ k → label i = label k → label j = label i)
    (b : β) :
    (Finset.univ.filter fun i => label i = b).card ≤ (matchingSpan f label b).card := by
  classical
  calc
    (Finset.univ.filter fun i => label i = b).card =
        ((Finset.univ.filter fun i => label i = b).image f).card :=
      (Finset.card_image_of_injective _ hf.injective).symm
    _ = (matchingSpan f label b ∩ Finset.univ.image f).card := by
      rw [matchingSpan_inter_image f hf label hc]
    _ ≤ (matchingSpan f label b).card := Finset.card_le_card Finset.inter_subset_left

/-- The two words' losses can be added because their total lengths are equal. -/
theorem matchingSpan_two_sided_gap_budget {r n : ℕ} {β : Type*} [DecidableEq β]
    (f g : Fin r → Fin n) (hf : StrictMono f) (hg : StrictMono g)
    (label : Fin r → β)
    (hc : ∀ {i j k}, i ≤ j → j ≤ k → label i = label k → label j = label i)
    (s : Finset β) :
    (∑ b ∈ s,
      (((matchingSpan f label b).card - (Finset.univ.filter fun i => label i = b).card) +
       ((matchingSpan g label b).card - (Finset.univ.filter fun i => label i = b).card)))
      ≤ 2 * (n - r) := by
  rw [Finset.sum_add_distrib, two_mul]
  exact Nat.add_le_add (matchingSpan_gap_budget f hf label hc s)
    (matchingSpan_gap_budget g hg label hc s)

/-- Specifying the first and last entries of a fiber gives its exact interval. -/
theorem matchingSpan_eq_Icc {r n : ℕ} {β : Type*} [DecidableEq β]
    (f : Fin r → Fin n) (hf : Monotone f) (label : Fin r → β)
    (b : β) (i j : Fin r) (hi : label i = b) (hj : label j = b)
    (hext : ∀ k, label k = b → i ≤ k ∧ k ≤ j) :
    matchingSpan f label b = Finset.Icc (f i) (f j) := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨a, c, ha, hc, hap, hpc⟩ := (mem_matchingSpan f label b p).mp hp
    exact Finset.mem_Icc.mpr ⟨(hf (hext a ha).1).trans hap,
      hpc.trans (hf (hext c hc).2)⟩
  · intro hp
    obtain ⟨hip, hpj⟩ := Finset.mem_Icc.mp hp
    exact (mem_matchingSpan f label b p).mpr ⟨i, j, hi, hj, hip, hpj⟩

/-- Every nonempty fiber admits endpoints describing the length of its span. -/
theorem matchingSpan_exists_endpoints {r n : ℕ} {β : Type*} [DecidableEq β]
    (f : Fin r → Fin n) (hf : Monotone f) (label : Fin r → β)
    (b : β) (hex : ∃ i, label i = b) :
    ∃ i j, label i = b ∧ label j = b ∧ i ≤ j ∧
      matchingSpan f label b = Finset.Icc (f i) (f j) ∧
      (matchingSpan f label b).card = (f j).val + 1 - (f i).val := by
  classical
  let fiber := Finset.univ.filter fun i => label i = b
  have hnon : fiber.Nonempty := by
    obtain ⟨i, hi⟩ := hex
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  let i := fiber.min' hnon
  let j := fiber.max' hnon
  have hi : label i = b := (Finset.mem_filter.mp (fiber.min'_mem hnon)).2
  have hj : label j = b := (Finset.mem_filter.mp (fiber.max'_mem hnon)).2
  have hext : ∀ k, label k = b → i ≤ k ∧ k ≤ j := by
    intro k hk
    have hmem : k ∈ fiber := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩
    exact ⟨fiber.min'_le k hmem, fiber.le_max' k hmem⟩
  have hspan := matchingSpan_eq_Icc f hf label b i j hi hj hext
  exact ⟨i, j, hi, hj, (hext j hj).1, hspan, by rw [hspan, Fin.card_Icc]⟩

/-- The concrete block-pair label of an increasing matching has convex fibers. -/
theorem block_pair_fiber_convex {r n : ℕ} (P : ℕ)
    (f g : Fin r → Fin n) (hf : Monotone f) (hg : Monotone g)
    {i j k : Fin r} (hij : i ≤ j) (hjk : j ≤ k)
    (heq : ((f i).val / P, (g i).val / P) = ((f k).val / P, (g k).val / P)) :
    ((f j).val / P, (g j).val / P) = ((f i).val / P, (g i).val / P) := by
  apply monotone_pair_fiber_convex (fun a => (f a).val / P)
    (fun a => (g a).val / P) _ _ hij hjk heq
  · intro a b hab
    exact Nat.div_le_div_right (hf hab)
  · intro a b hab
    exact Nat.div_le_div_right (hg hab)

/-- For the actual quotient block-pair labels, the span losses over any
selected pairs are at most twice the global one-sided matching deficit. -/
theorem block_pair_two_sided_gap_budget {r n : ℕ} (P : ℕ)
    (f g : Fin r → Fin n) (hf : StrictMono f) (hg : StrictMono g)
    (s : Finset (ℕ × ℕ)) :
    let label := fun i => ((f i).val / P, (g i).val / P)
    (∑ b ∈ s,
      (((matchingSpan f label b).card - (Finset.univ.filter fun i => label i = b).card) +
       ((matchingSpan g label b).card - (Finset.univ.filter fun i => label i = b).card)))
      ≤ 2 * (n - r) := by
  apply matchingSpan_two_sided_gap_budget f g hf hg
  intro i j k hij hjk heq
  exact block_pair_fiber_convex P f g hf.monotone hg.monotone hij hjk heq

/-- Every source span position remains in the source block of its pair. -/
theorem source_matchingSpan_block {r n : ℕ} (P : ℕ)
    (f g : Fin r → Fin n) (b : ℕ × ℕ) {p : Fin n}
    (hp : p ∈ matchingSpan f (fun i => ((f i).val / P, (g i).val / P)) b) :
    p.val / P = b.1 := by
  obtain ⟨i, j, hi, hj, hip, hpj⟩ :=
    (mem_matchingSpan f (fun i => ((f i).val / P, (g i).val / P)) b p).mp hp
  have hi' := congrArg Prod.fst hi
  have hj' := congrArg Prod.fst hj
  have hl := Nat.div_le_div_right (c := P) (show (f i).val ≤ p.val from hip)
  have hr := Nat.div_le_div_right (c := P) (show p.val ≤ (f j).val from hpj)
  omega

/-- Every target span position remains in the target block of its pair. -/
theorem target_matchingSpan_block {r n : ℕ} (P : ℕ)
    (f g : Fin r → Fin n) (b : ℕ × ℕ) {p : Fin n}
    (hp : p ∈ matchingSpan g (fun i => ((f i).val / P, (g i).val / P)) b) :
    p.val / P = b.2 := by
  obtain ⟨i, j, hi, hj, hip, hpj⟩ :=
    (mem_matchingSpan g (fun i => ((f i).val / P, (g i).val / P)) b p).mp hp
  have hi' := congrArg Prod.snd hi
  have hj' := congrArg Prod.snd hj
  have hl := Nat.div_le_div_right (c := P) (show (g i).val ≤ p.val from hip)
  have hr := Nat.div_le_div_right (c := P) (show p.val ≤ (g j).val from hpj)
  omega

/-- A span between two positions in one block fits within that block after
subtracting its initial block offset. -/
theorem same_block_interval_length {P A B : ℕ} (hP : 0 < P)
    (hAB : A ≤ B) (hblock : A / P = B / P) :
    A % P + (B + 1 - A) ≤ P ∧ B + 1 - A ≤ P := by
  have hA := Nat.mod_add_div A P
  have hB := Nat.mod_add_div B P
  rw [hblock] at hA
  have hmod := Nat.mod_lt B hP
  omega

end
end TreeEdit.BinaryLower

end OAI
