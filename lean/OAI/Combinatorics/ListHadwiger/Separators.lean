import OAI.Combinatorics.ListHadwiger.Basic

namespace OAI

namespace LinearListHadwiger

namespace SeparatorSplit

variable {V : Type} [DecidableEq V] {G : SimpleGraph V} {S V₁ Z V₂ : Finset V}

lemma swap (h : SeparatorSplit G S V₁ Z V₂) : SeparatorSplit G S V₂ Z V₁ := by
  refine ⟨?_, h.sep_right.symm, h.left_right.symm, h.left_sep.symm,
    h.right_nonempty, h.left_nonempty, ?_⟩
  · simpa only [Finset.union_comm, Finset.union_left_comm, Finset.union_assoc] using h.union_eq
  · intro v hv w hw hadj
    exact h.anticomplete w hw v hv hadj.symm

lemma left_union_subset (h : SeparatorSplit G S V₁ Z V₂) : V₁ ∪ Z ⊆ S := by
  rw [← h.union_eq]
  exact Finset.subset_union_left

lemma right_subset (h : SeparatorSplit G S V₁ Z V₂) : V₂ ⊆ S := by
  rw [← h.union_eq]
  exact Finset.subset_union_right

lemma left_union_disjoint (h : SeparatorSplit G S V₁ Z V₂) : Disjoint (V₁ ∪ Z) V₂ :=
  Finset.disjoint_union_left.mpr ⟨h.left_right, h.sep_right⟩

lemma sum_eq (h : SeparatorSplit G S V₁ Z V₂) (f : V → ℕ) :
    ∑ v ∈ S, f v = (∑ v ∈ V₁, f v) + (∑ v ∈ Z, f v) + ∑ v ∈ V₂, f v := by
  rw [← h.union_eq, Finset.sum_union h.left_union_disjoint, Finset.sum_union h.left_sep]

lemma left_union_ssubset (h : SeparatorSplit G S V₁ Z V₂) : V₁ ∪ Z ⊂ S := by
  refine Finset.ssubset_iff_subset_ne.mpr ⟨h.left_union_subset, ?_⟩
  intro heq
  obtain ⟨v, hv⟩ := h.right_nonempty
  exact Finset.disjoint_left.mp h.left_union_disjoint (heq.symm ▸ h.right_subset hv) hv

end SeparatorSplit

lemma constraintCost_restrict {V Color : Type} [DecidableEq V]
    (S A : Finset V) (k : ℕ) (B : V → Finset Color) :
    constraintCost S k (A ∩ S) B = constraintCost S k A B := by
  apply Finset.sum_congr rfl
  intro v hv
  simp [vertexCost, hv]

lemma precolor_cost_le {V Color : Type} [DecidableEq V]
    (S A : Finset V) (k : ℕ) (B : V → Finset Color) :
    k * (A ∩ S).card ≤ constraintCost S k A B := by
  rw [← constraintCost_restrict S A k B, constraintCost_eq S (A ∩ S) k B Finset.inter_subset_right]
  exact Nat.le_add_right _ _

lemma exists_balanced_separator {V Color : Type} [DecidableEq V]
    (G : SimpleGraph V) (S A : Finset V) (B : V → Finset Color) {k : ℕ}
    (hord : k < S.card) (hn : ¬KConnectedOn G S k)
    (hbudget : constraintCost S k A B ≤ 2 * k ^ 2) :
    ∃ V₁ Z V₂, Z.card < k ∧ SeparatorSplit G S V₁ Z V₂ ∧
      constraintCost V₂ k A B ≤ k ^ 2 := by
  obtain ⟨V₁, Z, V₂, hZ, hs⟩ := exists_separator G S hord hn
  have heq := hs.sum_eq (vertexCost k A B)
  change constraintCost S k A B = constraintCost V₁ k A B +
    constraintCost Z k A B + constraintCost V₂ k A B at heq
  by_cases hle : constraintCost V₂ k A B ≤ constraintCost V₁ k A B
  · exact ⟨V₁, Z, V₂, hZ, hs, by omega⟩
  · exact ⟨V₂, Z, V₁, hZ, hs.swap, by omega⟩

noncomputable def extraForbidden {V Color : Type} [DecidableEq V]
    (Z : Finset V) (B : V → Finset Color) (F : Finset Color) : V → Finset Color := by
  classical
  exact fun v => if v ∈ Z then B v ∪ F else B v

lemma extraForbidden_subset {V Color : Type} [DecidableEq V]
    (Z : Finset V) (B : V → Finset Color) (F : Finset Color) (v : V) :
    B v ⊆ extraForbidden Z B F v := by
  classical
  by_cases hv : v ∈ Z <;> simp [extraForbidden, hv]

lemma extraForbidden_cost {V Color : Type} [DecidableEq V]
    (S A Z : Finset V) (k : ℕ) (B : V → Finset Color) (F : Finset Color)
    (hZS : Z ⊆ S) :
    constraintCost S k A (extraForbidden Z B F) ≤
      constraintCost S k A B + Z.card * F.card := by
  classical
  have hpoint : ∀ v ∈ S, vertexCost k A (extraForbidden Z B F) v ≤
      vertexCost k A B v + (if v ∈ Z then F.card else 0) := by
    intro v _
    by_cases ha : v ∈ A <;> by_cases hz : v ∈ Z
    · simp [vertexCost, ha, hz]
    · simp [vertexCost, ha, hz]
    · simpa [vertexCost, extraForbidden, ha, hz] using Finset.card_union_le (B v) F
    · simp [vertexCost, extraForbidden, ha, hz]
  have heq : (∑ v ∈ S, if v ∈ Z then F.card else 0) = Z.card * F.card := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hZS]
    simp
  calc
    _ ≤ ∑ v ∈ S, (vertexCost k A B v + if v ∈ Z then F.card else 0) :=
      Finset.sum_le_sum hpoint
    _ = _ := by rw [Finset.sum_add_distrib, heq]; rfl

lemma first_side_cost {V Color : Type} [DecidableEq V] [DecidableEq Color]
    {G : SimpleGraph V} {S V₁ Z V₂ : Finset V}
    (hs : SeparatorSplit G S V₁ Z V₂) (A : Finset V) (B : V → Finset Color)
    (φ : V → Color) {k : ℕ} (hZ : Z.card ≤ k) :
    constraintCost (V₁ ∪ Z) k (A ∩ (V₁ ∪ Z))
      (extraForbidden Z B ((A ∩ V₂).image φ)) ≤ constraintCost S k A B := by
  classical
  rw [constraintCost_restrict]
  have heq : constraintCost (V₁ ∪ Z) k A B + constraintCost V₂ k A B =
      constraintCost S k A B := by
    unfold constraintCost
    rw [← Finset.sum_union hs.left_union_disjoint, hs.union_eq]
  calc
    _ ≤ constraintCost (V₁ ∪ Z) k A B + Z.card * ((A ∩ V₂).image φ).card :=
      extraForbidden_cost _ _ _ _ _ _ Finset.subset_union_right
    _ ≤ constraintCost (V₁ ∪ Z) k A B + k * (A ∩ V₂).card := by
      gcongr
      exact Finset.card_image_le
    _ ≤ constraintCost (V₁ ∪ Z) k A B + constraintCost V₂ k A B :=
      Nat.add_le_add_left (precolor_cost_le V₂ A k B) _
    _ = _ := heq

lemma second_side_cost {V Color : Type} [DecidableEq V]
    {G : SimpleGraph V} {S V₁ Z V₂ : Finset V}
    (hs : SeparatorSplit G S V₁ Z V₂) (A : Finset V) (B : V → Finset Color) (k : ℕ) :
    constraintCost (V₂ ∪ Z) k (Z ∪ (A ∩ V₂)) B =
      k * Z.card + constraintCost V₂ k A B := by
  classical
  unfold constraintCost
  rw [Finset.sum_union hs.sep_right.symm]
  have hright : (∑ v ∈ V₂, vertexCost k (Z ∪ (A ∩ V₂)) B v) =
      ∑ v ∈ V₂, vertexCost k A B v := by
    apply Finset.sum_congr rfl
    intro v hv
    have hz : v ∉ Z := fun hz => Finset.disjoint_left.mp hs.sep_right hz hv
    simp [vertexCost, hv, hz]
  have hsep : (∑ v ∈ Z, vertexCost k (Z ∪ (A ∩ V₂)) B v) = k * Z.card := by
    calc
      _ = ∑ _v ∈ Z, k := Finset.sum_congr rfl (fun v hv => by simp [vertexCost, hv])
      _ = _ := by simp [Nat.mul_comm]
  rw [hright, hsep, Nat.add_comm]

lemma SeparatorSplit.glue {V Color : Type} [DecidableEq V]
    {G : SimpleGraph V} {S V₁ Z V₂ : Finset V}
    (hs : SeparatorSplit G S V₁ Z V₂) {L : V → Finset Color} {c₁ c₂ : V → Color}
    (h₁ : ValidOn G (V₁ ∪ Z) L c₁) (h₂ : ValidOn G (V₂ ∪ Z) L c₂)
    (hagree : ∀ v ∈ Z, c₁ v = c₂ v) :
    ∃ c, ValidOn G S L c ∧ (∀ v ∈ V₁ ∪ Z, c v = c₁ v) ∧
      ∀ v ∈ V₂ ∪ Z, c v = c₂ v := by
  classical
  let c : V → Color := fun v => if v ∈ V₂ then c₂ v else c₁ v
  have hc₁ : ∀ v ∈ V₁ ∪ Z, c v = c₁ v := by
    intro v hv
    have hn : v ∉ V₂ := fun hh => Finset.disjoint_left.mp hs.left_union_disjoint hv hh
    exact ite_eq_right hn
  have hc₂ : ∀ v ∈ V₂ ∪ Z, c v = c₂ v := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact ite_eq_left hv
    · rw [hc₁ v (Finset.mem_union_right _ hv), hagree v hv]
  have hcover : ∀ v ∈ S, v ∈ V₁ ∪ Z ∨ v ∈ V₂ := by
    intro v hv
    rw [← hs.union_eq] at hv
    exact Finset.mem_union.mp hv
  refine ⟨c, ⟨?_, ?_⟩, hc₁, hc₂⟩
  · intro v hv
    rcases hcover v hv with hv | hv
    · rw [hc₁ v hv]
      exact h₁.1 v hv
    · rw [hc₂ v (Finset.mem_union_left _ hv)]
      exact h₂.1 v (Finset.mem_union_left _ hv)
  · intro v hv w hw hadj
    rcases hcover v hv with hv | hv <;> rcases hcover w hw with hw | hw
    · rw [hc₁ v hv, hc₁ w hw]
      exact h₁.2 hv hw hadj
    · rcases Finset.mem_union.mp hv with hv | hv
      · exact (hs.anticomplete v hv w hw hadj).elim
      · have hv' : v ∈ V₂ ∪ Z := Finset.mem_union_right _ hv
        have hw' : w ∈ V₂ ∪ Z := Finset.mem_union_left _ hw
        rw [hc₂ v hv', hc₂ w hw']
        exact h₂.2 hv' hw' hadj
    · rcases Finset.mem_union.mp hw with hw | hw
      · exact (hs.anticomplete w hw v hv hadj.symm).elim
      · have hv' : v ∈ V₂ ∪ Z := Finset.mem_union_left _ hv
        have hw' : w ∈ V₂ ∪ Z := Finset.mem_union_right _ hw
        rw [hc₂ v hv', hc₂ w hw']
        exact h₂.2 hv' hw' hadj
    · have hv' : v ∈ V₂ ∪ Z := Finset.mem_union_left _ hv
      have hw' : w ∈ V₂ ∪ Z := Finset.mem_union_left _ hw
      rw [hc₂ v hv', hc₂ w hw']
      exact h₂.2 hv' hw' hadj

lemma separator_precolor {V Color : Type} [DecidableEq V]
    {G : SimpleGraph V} {S V₁ Z V₂ : Finset V}
    (hs : SeparatorSplit G S V₁ Z V₂) (A : Finset V) (L : V → Finset Color)
    (φ c₁ : V → Color) (hφ : ValidOn G A L φ) (h₁ : ValidOn G (V₁ ∪ Z) L c₁)
    (hcompat : ∀ v ∈ Z, ∀ w ∈ A ∩ V₂, G.Adj v w → c₁ v ≠ φ w) :
    ∃ φ₂, ValidOn G (Z ∪ (A ∩ V₂)) L φ₂ ∧
      (∀ v ∈ Z, φ₂ v = c₁ v) ∧ (∀ v ∈ A ∩ V₂, φ₂ v = φ v) := by
  classical
  let φ₂ := fun v => if v ∈ Z then c₁ v else φ v
  have hz : ∀ v ∈ Z, φ₂ v = c₁ v := fun v hv => ite_eq_left hv
  have hd : ∀ v ∈ A ∩ V₂, φ₂ v = φ v := by
    intro v hv
    exact ite_eq_right (fun hh => Finset.disjoint_left.mp hs.sep_right hh (Finset.mem_inter.mp hv).2)
  refine ⟨φ₂, ⟨?_, ?_⟩, hz, hd⟩
  · intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · rw [hz v hv]
      exact h₁.1 v (Finset.mem_union_right _ hv)
    · rw [hd v hv]
      exact hφ.1 v (Finset.mem_inter.mp hv).1
  · intro v hv w hw hadj
    rcases Finset.mem_union.mp hv with hv | hv <;>
      rcases Finset.mem_union.mp hw with hw | hw
    · rw [hz v hv, hz w hw]
      exact h₁.2 (Finset.mem_union_right _ hv) (Finset.mem_union_right _ hw) hadj
    · rw [hz v hv, hd w hw]
      exact hcompat v hv w hw hadj
    · rw [hd v hv, hz w hw]
      exact (hcompat w hw v hv hadj.symm).symm
    · rw [hd v hv, hd w hw]
      exact hφ.2 (Finset.mem_inter.mp hv).1 (Finset.mem_inter.mp hw).1 hadj

theorem constrained_coloring_on {V Color : Type} [DecidableEq V]
    (G : SimpleGraph V) (S A : Finset V) (L B : V → Finset Color) (φ : V → Color)
    {k m : ℕ} (hk : 1 ≤ k) (hAS : A ⊆ S)
    (hconn : ∀ T ⊆ S, KConnectedOn G T k → Choosable (G.induce (↑T : Set V)) m)
    (hL : ∀ v ∈ S, m + 6 * k ≤ (L v).card) (hφ : ValidOn G A L φ)
    (hB : ∀ v ∈ S \ A, (B v).card < k)
    (hbudget : constraintCost S k A B ≤ 2 * k ^ 2) :
    ∃ c, ValidOn G S L c ∧ (∀ v ∈ A, c v = φ v) ∧
      ∀ v ∈ S \ A, c v ∉ B v := by
  classical
  induction S using Finset.strongInductionOn generalizing A B φ with
  | _ S ih =>
    have hAc : A.card ≤ 2 * k := constraintCost_card_bound hk hAS hbudget
    by_cases hsmall : S.card ≤ 2 * k
    · have hchoose : Choosable (G.induce (↑(S \ A) : Set V)) (S \ A).card := by
        have hh := choosable_card (G.induce (↑(S \ A) : Set V))
        change Choosable _ (Fintype.card ↥(S \ A)) at hh
        rw [Fintype.card_coe] at hh
        exact hh
      apply extend_from_choosable G S A L B φ hφ hchoose
      intro v hv
      have hh := hB v hv
      have hl := hL v (Finset.mem_sdiff.mp hv).1
      have heq := Finset.card_sdiff_add_card_eq_card hAS
      omega
    by_cases hc : KConnectedOn G S k
    · have hchoose : Choosable (G.induce (↑(S \ A) : Set V)) m :=
        choosable_induce_subset (hconn S Finset.Subset.rfl hc) Finset.sdiff_subset
      apply extend_from_choosable G S A L B φ hφ hchoose
      intro v hv
      have hh := hB v hv
      have hl := hL v (Finset.mem_sdiff.mp hv).1
      omega
    obtain ⟨V₁, Z, V₂, hZk, hs, hbal⟩ :=
      exists_balanced_separator G S A B (by omega) hc hbudget
    have hS₁ := hs.left_union_subset
    have hS₂ := hs.swap.left_union_subset
    let A₁ := A ∩ (V₁ ∪ Z)
    let B₁ := extraForbidden Z B ((A ∩ V₂).image φ)
    have hA₁ : A₁ ⊆ V₁ ∪ Z := Finset.inter_subset_right
    have hbudget₁ : constraintCost (V₁ ∪ Z) k A₁ B₁ ≤ 2 * k ^ 2 :=
      (first_side_cost hs A B φ hZk.le).trans hbudget
    have hB₁ : ∀ v ∈ (V₁ ∪ Z) \ A₁, (B₁ v).card < 3 * k := by
      intro v hv
      have hvS₁ := (Finset.mem_sdiff.mp hv).1
      have hvA : v ∉ A := fun ha => (Finset.mem_sdiff.mp hv).2 (Finset.mem_inter.mpr ⟨ha, hvS₁⟩)
      have hb := hB v (Finset.mem_sdiff.mpr ⟨hS₁ hvS₁, hvA⟩)
      have hd : ((A ∩ V₂).image φ).card ≤ 2 * k :=
        Finset.card_image_le.trans ((Finset.card_le_card Finset.inter_subset_left).trans hAc)
      by_cases hz : v ∈ Z
      · have hu := Finset.card_union_le (B v) ((A ∩ V₂).image φ)
        simp only [B₁, extraForbidden, ite_eq_left hz]
        omega
      · simpa only [B₁, extraForbidden, ite_eq_right hz] using (show (B v).card < 3 * k by omega)
    obtain ⟨A₁', φ₁, hA₁A₁', hA₁'S₁, hφ₁, hext₁, hav₁, hlow₁, hcost₁⟩ :=
      promote_constraints G (V₁ ∪ Z) A₁ L B₁ φ hk hA₁
        (fun v hv => hL v (hS₁ hv)) (hφ.mono Finset.inter_subset_left) hB₁ hbudget₁
    obtain ⟨c₁, hc₁, hc₁ext, hc₁av⟩ :=
      ih (V₁ ∪ Z) hs.left_union_ssubset A₁' B₁ φ₁ hA₁'S₁
        (fun T hT => hconn T (hT.trans hS₁)) (fun v hv => hL v (hS₁ hv))
        hφ₁ hlow₁ (hcost₁.trans hbudget₁)
    have hc₁orig : ∀ v ∈ A₁, c₁ v = φ v := fun v hv =>
      (hc₁ext v (hA₁A₁' hv)).trans (hext₁ v hv)
    have hc₁avoid : ∀ v ∈ (V₁ ∪ Z) \ A₁, c₁ v ∉ B₁ v := by
      intro v hv
      by_cases ha : v ∈ A₁'
      · rw [hc₁ext v ha]
        exact hav₁ v (Finset.mem_sdiff.mpr ⟨ha, (Finset.mem_sdiff.mp hv).2⟩)
      · exact hc₁av v (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hv).1, ha⟩)
    have hcompat : ∀ v ∈ Z, ∀ w ∈ A ∩ V₂, G.Adj v w → c₁ v ≠ φ w := by
      intro v hv w hw hadj
      have hvS₁ : v ∈ V₁ ∪ Z := Finset.mem_union_right _ hv
      by_cases ha : v ∈ A
      · rw [hc₁orig v (Finset.mem_inter.mpr ⟨ha, hvS₁⟩)]
        exact hφ.2 ha (Finset.mem_inter.mp hw).1 hadj
      · intro heq
        have hva₁ : v ∉ A₁ := fun hh => ha (Finset.mem_inter.mp hh).1
        apply hc₁avoid v (Finset.mem_sdiff.mpr ⟨hvS₁, hva₁⟩)
        rw [heq]
        simp only [B₁, extraForbidden, ite_eq_left hv]
        exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w, hw, rfl⟩)
    obtain ⟨φ₂, hφ₂, hφ₂Z, hφ₂D⟩ := separator_precolor hs A L φ c₁ hφ hc₁ hcompat
    let A₂ := Z ∪ (A ∩ V₂)
    have hA₂S₂ : A₂ ⊆ V₂ ∪ Z := by
      intro v hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact Finset.mem_union_right _ hv
      · exact Finset.mem_union_left _ (Finset.mem_inter.mp hv).2
    have hbudget₂ : constraintCost (V₂ ∪ Z) k A₂ B ≤ 2 * k ^ 2 := by
      rw [show A₂ = Z ∪ (A ∩ V₂) from rfl, second_side_cost hs A B k]
      have hmul : k * Z.card ≤ k ^ 2 := by
        calc
          k * Z.card ≤ k * k := Nat.mul_le_mul_left k hZk.le
          _ = k ^ 2 := by ring
      omega
    have hB₂ : ∀ v ∈ (V₂ ∪ Z) \ A₂, (B v).card < k := by
      intro v hv
      have hvS₂ := (Finset.mem_sdiff.mp hv).1
      have hn := (Finset.mem_sdiff.mp hv).2
      have hnZ : v ∉ Z := fun hh => hn (Finset.mem_union_left _ hh)
      have hvV₂ : v ∈ V₂ := (Finset.mem_union.mp hvS₂).resolve_right hnZ
      have hnA : v ∉ A := fun hh => hn (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hh, hvV₂⟩))
      exact hB v (Finset.mem_sdiff.mpr ⟨hS₂ hvS₂, hnA⟩)
    obtain ⟨c₂, hc₂, hc₂ext, hc₂av⟩ :=
      ih (V₂ ∪ Z) hs.swap.left_union_ssubset A₂ B φ₂ hA₂S₂
        (fun T hT => hconn T (hT.trans hS₂)) (fun v hv => hL v (hS₂ hv))
        hφ₂ hB₂ hbudget₂
    have hagree : ∀ v ∈ Z, c₁ v = c₂ v := by
      intro v hv
      rw [hc₂ext v (Finset.mem_union_left _ hv), hφ₂Z v hv]
    obtain ⟨c, hc, hcS₁, hcS₂⟩ := hs.glue hc₁ hc₂ hagree
    refine ⟨c, hc, ?_, ?_⟩
    · intro v hv
      have hvS := hAS hv
      rw [← hs.union_eq] at hvS
      rcases Finset.mem_union.mp hvS with hvS₁ | hvV₂
      · rw [hcS₁ v hvS₁]
        exact hc₁orig v (Finset.mem_inter.mpr ⟨hv, hvS₁⟩)
      · have hvD : v ∈ A ∩ V₂ := Finset.mem_inter.mpr ⟨hv, hvV₂⟩
        rw [hcS₂ v (Finset.mem_union_left _ hvV₂),
          hc₂ext v (Finset.mem_union_right _ hvD), hφ₂D v hvD]
    · intro v hv
      have hvS := (Finset.mem_sdiff.mp hv).1
      have hnA := (Finset.mem_sdiff.mp hv).2
      rw [← hs.union_eq] at hvS
      rcases Finset.mem_union.mp hvS with hvS₁ | hvV₂
      · rw [hcS₁ v hvS₁]
        have hnA₁ : v ∉ A₁ := fun hh => hnA (Finset.mem_inter.mp hh).1
        exact fun hh => hc₁avoid v (Finset.mem_sdiff.mpr ⟨hvS₁, hnA₁⟩)
          (extraForbidden_subset Z B ((A ∩ V₂).image φ) v hh)
      · have hvS₂ : v ∈ V₂ ∪ Z := Finset.mem_union_left _ hvV₂
        have hnZ : v ∉ Z := fun hh => Finset.disjoint_left.mp hs.sep_right hh hvV₂
        have hnA₂ : v ∉ A₂ := by
          intro hh
          rcases Finset.mem_union.mp hh with hh | hh
          · exact hnZ hh
          · exact hnA (Finset.mem_inter.mp hh).1
        rw [hcS₂ v hvS₂]
        exact hc₂av v (Finset.mem_sdiff.mpr ⟨hvS₂, hnA₂⟩)

theorem choosable_of_connected_induced {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {k m : ℕ} (hk : 1 ≤ k)
    (hconn : ∀ T : Finset V, KConnectedOn G T k →
      Choosable (G.induce (↑T : Set V)) m) : Choosable G (m + 6 * k) := by
  classical
  intro Color L hL
  have hn : ∀ v, (L v).Nonempty := by
    intro v
    apply Finset.card_pos.mp
    have hh := hL v
    omega
  choose φ hφ using hn
  obtain ⟨c, hc, _, _⟩ := constrained_coloring_on G Finset.univ ∅ L
    (fun _ => ∅) φ hk (Finset.empty_subset _)
    (fun T _ => hconn T) (fun v _ => hL v)
    ⟨by simp, by simp [ProperOn]⟩
    (by intro v hv; simpa using (show 0 < k by omega)) (by simp [constraintCost, vertexCost])
  exact ⟨c, fun v => hc.1 v (Finset.mem_univ _),
    fun _ _ h => hc.2 (Finset.mem_univ _) (Finset.mem_univ _) h⟩

theorem list_connectivity_extraction {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {k : ℕ} (hk : 1 ≤ k)
    (hlarge : 6 * k < listChromaticNumber G) :
    ∃ T : Finset V, KConnectedOn G T k ∧
      listChromaticNumber G - 6 * k ≤ listChromaticNumber (G.induce (↑T : Set V)) := by
  classical
  by_contra hn
  push Not at hn
  let m := listChromaticNumber G - 6 * k - 1
  have hconn : ∀ T : Finset V, KConnectedOn G T k →
      Choosable (G.induce (↑T : Set V)) m := by
    intro T hT
    apply (listChromaticNumber_le_iff _ _).mp
    have hh := hn T hT
    dsimp [m]
    omega
  have hchoose := choosable_of_connected_induced G hk hconn
  have hbound := (listChromaticNumber_le_iff G _).mpr hchoose
  dsimp [m] at hbound
  omega

lemma connected_induce_star {V : Type} (G : SimpleGraph V) (S : Set V)
    (r : V) (hr : r ∈ S) (hS : ∀ v ∈ S, v = r ∨ G.Adj r v) :
    (G.induce S).Connected := by
  have hre : ∀ v : S, (G.induce S).Reachable ⟨r, hr⟩ v := by
    intro v
    rcases hS v v.property with hv | hv
    · have he : v = ⟨r, hr⟩ := Subtype.ext hv
      rw [he]
    · exact (show (G.induce S).Adj ⟨r, hr⟩ v from hv).reachable
  exact { preconnected := fun u v => (hre u).symm.trans (hre v), nonempty := ⟨⟨r, hr⟩⟩ }

theorem cliqueMinor_of_subdivision {V : Type} {t : ℕ} (G : SimpleGraph V)
    (r : Fin t → V) (hr : Function.Injective r)
    (mid : {p : Fin t × Fin t // p.1 < p.2} → V)
    (hm : Function.Injective mid)
    (hd : ∀ p i, mid p ≠ r i)
    (ha : ∀ p, G.Adj (r p.val.1) (mid p) ∧ G.Adj (r p.val.2) (mid p)) :
    HasCliqueMinor G t := by
  let B : Fin t → Set V := fun i =>
    {v | v = r i ∨ ∃ j : Fin t, ∃ h : i < j, v = mid ⟨(i, j), h⟩}
  have hroot : ∀ i, r i ∈ B i := fun _ => Or.inl rfl
  have hc : ∀ i, (G.induce (B i)).Connected := by
    intro i
    apply connected_induce_star G (B i) (r i) (hroot i)
    intro v hv
    rcases hv with hv | ⟨j, hij, rfl⟩
    · exact Or.inl hv
    · exact Or.inr (ha ⟨(i, j), hij⟩).1
  refine ⟨B, hc, ?_, ?_⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro v hi hj
    rcases hi with rfl | ⟨a, hia, rfl⟩
    · rcases hj with he | ⟨b, hjb, he⟩
      · exact hij (hr he)
      · exact hd ⟨(j, b), hjb⟩ i he.symm
    · rcases hj with he | ⟨b, hjb, he⟩
      · exact hd ⟨(i, a), hia⟩ j he
      · have hh := hm he
        exact hij (congrArg (fun p => p.val.1) hh)
  · intro i j hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact ⟨mid ⟨(i, j), hij⟩, Or.inr ⟨j, hij, rfl⟩,
        r j, hroot j, (ha ⟨(i, j), hij⟩).2.symm⟩
    · exact ⟨r i, hroot i, mid ⟨(j, i), hji⟩,
        Or.inr ⟨i, hji, rfl⟩, (ha ⟨(j, i), hji⟩).2⟩

lemma cliqueMinor_of_saturated_pairs {V : Type} [DecidableEq V]
    {t : ℕ} (G : SimpleGraph V) (X S N : Finset V)
    (hSX : Disjoint S X) (hNX : N ⊆ X) (hN : t ≤ N.card)
    (f : V → Sym2 V)
    (hf : ∀ w ∈ S, ∀ a ∈ f w, G.Adj w a)
    (hsat : ∀ a ∈ N, ∀ b ∈ N, a ≠ b → ∃ w ∈ S, f w = s(a, b)) :
    HasCliqueMinor G t := by
  classical
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin t) (β := ↥N) (by simpa using hN)
  let r : Fin t → V := fun i => (e i).val
  have hr : Function.Injective r := fun i j h => e.injective (Subtype.ext h)
  have hrN : ∀ i, r i ∈ N := fun i => (e i).property
  have hw : ∀ p : {p : Fin t × Fin t // p.1 < p.2},
      ∃ w ∈ S, f w = s(r p.val.1, r p.val.2) := by
    intro p
    exact hsat _ (hrN _) _ (hrN _) (fun h => p.property.ne (hr h))
  choose mid hmS hmf using hw
  have hmi : Function.Injective mid := by
    intro p q hpq
    have he : s(r p.val.1, r p.val.2) = s(r q.val.1, r q.val.2) := by
      rw [← hmf p, ← hmf q, hpq]
    rcases Sym2.eq_iff.mp he with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Subtype.ext (Prod.ext (hr h₁) (hr h₂))
    · have h₁' := hr h₁
      have h₂' := hr h₂
      have hp := p.property
      have hq := q.property
      omega
  refine cliqueMinor_of_subdivision G r hr mid hmi ?_ ?_
  · intro p i heq
    exact Finset.disjoint_left.mp hSX (hmS p) (heq ▸ hNX (hrN i))
  · intro p
    constructor
    · apply (hf _ (hmS p) _ ?_).symm
      rw [hmf p]
      exact Sym2.mem_iff.mpr (Or.inl rfl)
    · apply (hf _ (hmS p) _ ?_).symm
      rw [hmf p]
      exact Sym2.mem_iff.mpr (Or.inr rfl)

noncomputable def neighborPairs {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (X : Finset V) (v : V) : Finset (Sym2 V) := by
  classical
  exact (X.filter (G.Adj v)).offDiag.image Sym2.mk.uncurry

lemma mem_neighborPairs {V : Type} [DecidableEq V] {G : SimpleGraph V} {X : Finset V}
    {v : V} {p : Sym2 V} (hp : p ∈ neighborPairs G X v) :
    ∀ a ∈ p, a ∈ X ∧ G.Adj v a := by
  classical
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨ha, hb, _⟩ := Finset.mem_offDiag.mp hab
  intro z hz
  rcases Sym2.mem_iff.mp hz with rfl | rfl
  · exact Finset.mem_filter.mp ha
  · exact Finset.mem_filter.mp hb

end LinearListHadwiger

end OAI
