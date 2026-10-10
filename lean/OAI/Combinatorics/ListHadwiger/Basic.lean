import OAI.Combinatorics.ListHadwiger.Model

namespace OAI

namespace LinearListHadwiger

theorem choosable_mono {V : Type} {G : SimpleGraph V} {k l : ℕ}
    (h : Choosable G k) (hkl : k ≤ l) : Choosable G l := by
  intro Color L hL
  exact h Color L (fun v => hkl.trans (hL v))

theorem choosable_card {V : Type} [Fintype V] (G : SimpleGraph V) :
    Choosable G (Fintype.card V) := by
  classical
  intro Color L hL
  have hall : ∀ s : Finset V, s.card ≤ (s.biUnion L).card := by
    intro s
    obtain rfl | hs := s.eq_empty_or_nonempty
    · simp
    obtain ⟨v, hv⟩ := hs
    exact (Finset.card_le_univ s).trans ((hL v).trans
      (Finset.card_le_card (Finset.subset_biUnion_of_mem L hv)))
  obtain ⟨c, hc, hmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective L).mp hall
  exact ⟨c, hmem, fun _ _ hvw heq => hvw.ne (hc heq)⟩

theorem choosable_listChromaticNumber {V : Type} [Fintype V] (G : SimpleGraph V) :
    Choosable G (listChromaticNumber G) := by
  exact Nat.sInf_mem (s := {k : ℕ | Choosable G k})
    ⟨Fintype.card V, choosable_card G⟩

theorem listChromaticNumber_le_iff {V : Type} [Fintype V] (G : SimpleGraph V)
    (k : ℕ) : listChromaticNumber G ≤ k ↔ Choosable G k := by
  constructor
  · exact fun h => choosable_mono (choosable_listChromaticNumber G) h
  · intro h
    exact Nat.sInf_le h

theorem listChromaticNumber_le_card {V : Type} [Fintype V] (G : SimpleGraph V) :
    listChromaticNumber G ≤ Fintype.card V :=
  (listChromaticNumber_le_iff G _).mpr (choosable_card G)

theorem cliqueMinor_order_le_card {V : Type} [Fintype V] {G : SimpleGraph V}
    {t : ℕ} (h : HasCliqueMinor G t) : t ≤ Fintype.card V := by
  classical
  obtain ⟨B, hc, hd, _⟩ := h
  have hb : ∀ i, ∃ v, v ∈ B i := fun i => by
    obtain ⟨v⟩ := (hc i).nonempty
    exact ⟨v.val, v.property⟩
  choose v hv using hb
  have hi : Function.Injective v := by
    intro i j hij
    by_contra hn
    exact Set.disjoint_left.mp (hd i j hn) (hv i) (by
      rw [hij]
      exact hv j)
  simpa using Fintype.card_le_of_injective v hi

theorem cliqueMinor_zero {V : Type} (G : SimpleGraph V) : HasCliqueMinor G 0 := by
  refine ⟨Fin.elim0, ?_, ?_, ?_⟩
  · exact fun i => Fin.elim0 i
  · exact fun i => Fin.elim0 i
  · exact fun i => Fin.elim0 i

theorem hadwiger_bddAbove {V : Type} [Fintype V] (G : SimpleGraph V) :
    BddAbove {t : ℕ | HasCliqueMinor G t} :=
  ⟨Fintype.card V, fun _ h => cliqueMinor_order_le_card h⟩

theorem cliqueMinor_le_hadwigerNumber {V : Type} [Fintype V] {G : SimpleGraph V}
    {t : ℕ} (h : HasCliqueMinor G t) : t ≤ hadwigerNumber G :=
  le_csSup (hadwiger_bddAbove G) h

theorem hasCliqueMinor_hadwigerNumber {V : Type} [Fintype V] (G : SimpleGraph V) :
    HasCliqueMinor G (hadwigerNumber G) := by
  exact Nat.sSup_mem ⟨0, cliqueMinor_zero G⟩ (hadwiger_bddAbove G)

theorem cliqueMinor_one {V : Type} [Nonempty V] (G : SimpleGraph V) :
    HasCliqueMinor G 1 := by
  classical
  let v : V := Classical.choice inferInstance
  refine ⟨fun _ => {v}, ?_, ?_, ?_⟩
  · intro i
    exact SimpleGraph.Connected.of_subsingleton
  · intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  · intro i j hij
    exact (hij (Subsingleton.elim i j)).elim

theorem one_le_hadwigerNumber {V : Type} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) : 1 ≤ hadwigerNumber G :=
  cliqueMinor_le_hadwigerNumber (cliqueMinor_one G)

def KConnectedOn {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) (k : ℕ) : Prop :=
  k < S.card ∧ ∀ Z ⊆ S, Z.card < k → (G.induce (↑(S \ Z) : Set V)).Connected

structure SeparatorSplit {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (S V₁ Z V₂ : Finset V) : Prop where
  union_eq : V₁ ∪ Z ∪ V₂ = S
  left_sep : Disjoint V₁ Z
  left_right : Disjoint V₁ V₂
  sep_right : Disjoint Z V₂
  left_nonempty : V₁.Nonempty
  right_nonempty : V₂.Nonempty
  anticomplete : ∀ v ∈ V₁, ∀ w ∈ V₂, ¬G.Adj v w

lemma exists_separator {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) {k : ℕ} (hord : k < S.card) (hn : ¬KConnectedOn G S k) :
    ∃ V₁ Z V₂, Z.card < k ∧ SeparatorSplit G S V₁ Z V₂ := by
  classical
  obtain ⟨Z, hZS, hZk, hZ⟩ : ∃ Z ⊆ S,
      Z.card < k ∧ ¬(G.induce (↑(S \ Z) : Set V)).Connected := by
    simpa only [KConnectedOn, not_and, hord, forall_const, not_forall,
      exists_prop, Classical.not_imp] using hn
  let T := S \ Z
  let H := G.induce (↑T : Set V)
  have hT : T.Nonempty := by
    have heq := Finset.card_sdiff_add_card_eq_card hZS
    exact Finset.card_pos.mp (by dsimp [T]; omega)
  have hnpre : ¬H.Preconnected := by
    intro h
    apply hZ
    obtain ⟨v, hv⟩ := hT
    exact { preconnected := h, nonempty := ⟨⟨v, hv⟩⟩ }
  obtain ⟨u, v, huv⟩ : ∃ u v, ¬H.Reachable u v := by
    simpa only [SimpleGraph.Preconnected, not_forall] using hnpre
  let V₁ := T.filter (fun x => ∃ hx : x ∈ T, H.Reachable u ⟨x, hx⟩)
  let V₂ := T \ V₁
  have h₁T : V₁ ⊆ T := Finset.filter_subset _ _
  have h₂T : V₂ ⊆ T := Finset.sdiff_subset
  have hu : u.val ∈ V₁ := by
    exact Finset.mem_filter.mpr ⟨u.property, u.property, SimpleGraph.Reachable.rfl⟩
  have hv : v.val ∈ V₂ := by
    refine Finset.mem_sdiff.mpr ⟨v.property, ?_⟩
    intro h
    obtain ⟨_, hx, hr⟩ := Finset.mem_filter.mp h
    exact huv hr
  refine ⟨V₁, Z, V₂, hZk, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ⟨u.val, hu⟩, ⟨v.val, hv⟩, ?_⟩
  · ext x
    simp only [Finset.mem_union]
    have hsub : x ∈ V₁ → x ∈ S ∧ x ∉ Z := fun hx => Finset.mem_sdiff.mp (h₁T hx)
    have hZsub : x ∈ Z → x ∈ S := fun hx => hZS hx
    simp only [V₂, T, Finset.mem_sdiff]
    tauto
  · exact Finset.disjoint_left.mpr (fun x hx hz => (Finset.mem_sdiff.mp (h₁T hx)).2 hz)
  · exact Finset.disjoint_left.mpr (fun x hx hx₂ => (Finset.mem_sdiff.mp hx₂).2 hx)
  · exact Finset.disjoint_left.mpr (fun x hz hx => (Finset.mem_sdiff.mp (h₂T hx)).2 hz)
  · intro x hx y hy hxy
    obtain ⟨_, hxT, hr⟩ := Finset.mem_filter.mp hx
    have hyT := h₂T hy
    have hay : H.Adj ⟨x, hxT⟩ ⟨y, hyT⟩ := hxy
    have hy₁ : y ∈ V₁ := Finset.mem_filter.mpr ⟨hyT, hyT, hr.trans hay.reachable⟩
    exact (Finset.mem_sdiff.mp hy).2 hy₁

lemma choosable_induce {V : Type} {G : SimpleGraph V} {k : ℕ}
    (h : Choosable G k) (S : Set V) : Choosable (G.induce S) k := by
  classical
  intro Color L hL
  let ei : Color ↪ Color ⊕ Fin k := ⟨Sum.inl, Sum.inl_injective⟩
  let eo : Fin k ↪ Color ⊕ Fin k := ⟨Sum.inr, Sum.inr_injective⟩
  let L' : V → Finset (Color ⊕ Fin k) := fun v =>
    if hv : v ∈ S then (L ⟨v, hv⟩).map ei else Finset.univ.map eo
  have hL' : ∀ v, k ≤ (L' v).card := by
    intro v
    by_cases hv : v ∈ S
    · simpa [L', hv] using hL ⟨v, hv⟩
    · simp [L', hv]
  obtain ⟨c, hc, hp⟩ := h _ L' hL'
  have hex : ∀ x : S, ∃ a ∈ L x, c x = Sum.inl a := by
    intro x
    have hh := hc x.val
    simp only [L', dite_eq_left x.property, Finset.mem_map] at hh
    obtain ⟨a, ha, heq⟩ := hh
    exact ⟨a, ha, heq.symm⟩
  choose f hf heq using hex
  refine ⟨f, hf, ?_⟩
  intro v w hvw hfw
  apply hp hvw
  change c v.val = c w.val
  rw [heq v, heq w, hfw]

def ProperOn {V Color : Type} (G : SimpleGraph V) (S : Finset V)
    (c : V → Color) : Prop :=
  ∀ ⦃v⦄, v ∈ S → ∀ ⦃w⦄, w ∈ S → G.Adj v w → c v ≠ c w

def ValidOn {V Color : Type} (G : SimpleGraph V) (S : Finset V)
    (L : V → Finset Color) (c : V → Color) : Prop :=
  (∀ v ∈ S, c v ∈ L v) ∧ ProperOn G S c

lemma ValidOn.mono {V Color : Type} {G : SimpleGraph V} {S T : Finset V}
    {L : V → Finset Color} {c : V → Color} (h : ValidOn G S L c)
    (hTS : T ⊆ S) : ValidOn G T L c :=
  ⟨fun v hv => h.1 v (hTS hv), fun _ hv _ hw => h.2 (hTS hv) (hTS hw)⟩

lemma extend_from_choosable {V Color : Type} [DecidableEq V]
    (G : SimpleGraph V) (S A : Finset V) (L B : V → Finset Color) (φ : V → Color)
    {m : ℕ} (hφ : ValidOn G A L φ)
    (hchoose : Choosable (G.induce (↑(S \ A) : Set V)) m)
    (hsizes : ∀ v ∈ S \ A, m + (B v).card + A.card ≤ (L v).card) :
    ∃ c, ValidOn G S L c ∧ (∀ v ∈ A, c v = φ v) ∧
      ∀ v ∈ S \ A, c v ∉ B v := by
  classical
  let L' : (↑(S \ A) : Set V) → Finset Color := fun v => L v \ (B v ∪ A.image φ)
  have hs : ∀ v, m ≤ (L' v).card := by
    intro v
    have h₁ : (L v.val).card ≤ (L v.val \ (B v.val ∪ A.image φ)).card +
        (B v.val ∪ A.image φ).card := Finset.card_le_card_sdiff_add_card
    have h₂ := Finset.card_union_le (B v.val) (A.image φ)
    have h₃ : (A.image φ).card ≤ A.card := Finset.card_image_le
    have h₄ := hsizes v.val v.property
    dsimp [L']
    omega
  obtain ⟨f, hf, hp⟩ := hchoose Color L' hs
  let c : V → Color := fun v => if hv : v ∈ S \ A then f ⟨v, hv⟩ else φ v
  have hcA : ∀ v ∈ A, c v = φ v := by
    intro v hv
    simp only [c, dite_eq_right (show v ∉ S \ A from fun h => (Finset.mem_sdiff.mp h).2 hv)]
  have hcmem : ∀ v ∈ S \ A, c v ∈ L v ∧ c v ∉ B v ∧ c v ∉ A.image φ := by
    intro v hv
    have hh := hf ⟨v, hv⟩
    simp only [c, dite_eq_left hv]
    simpa only [L', Finset.mem_sdiff, Finset.mem_union, not_or] using hh
  refine ⟨c, ⟨?_, ?_⟩, hcA, fun v hv => (hcmem v hv).2.1⟩
  · intro v hv
    by_cases ha : v ∈ A
    · rw [hcA v ha]
      exact hφ.1 v ha
    · exact (hcmem v (Finset.mem_sdiff.mpr ⟨hv, ha⟩)).1
  · intro v hv w hw hvw
    by_cases hva : v ∈ A <;> by_cases hwa : w ∈ A
    · rw [hcA v hva, hcA w hwa]
      exact hφ.2 hva hwa hvw
    · intro heq
      have hws : w ∈ S \ A := Finset.mem_sdiff.mpr ⟨hw, hwa⟩
      apply (hcmem w hws).2.2
      rw [← heq, hcA v hva]
      exact Finset.mem_image.mpr ⟨v, hva, rfl⟩
    · intro heq
      have hvs : v ∈ S \ A := Finset.mem_sdiff.mpr ⟨hv, hva⟩
      apply (hcmem v hvs).2.2
      rw [heq, hcA w hwa]
      exact Finset.mem_image.mpr ⟨w, hwa, rfl⟩
    · have hvs : v ∈ S \ A := Finset.mem_sdiff.mpr ⟨hv, hva⟩
      have hws : w ∈ S \ A := Finset.mem_sdiff.mpr ⟨hw, hwa⟩
      simpa only [c, dite_eq_left hvs, dite_eq_left hws] using
        (hp (v := ⟨v, hvs⟩) (w := ⟨w, hws⟩) hvw)

def vertexCost {V Color : Type} [DecidableEq V] (k : ℕ)
    (A : Finset V) (B : V → Finset Color) (v : V) : ℕ :=
  if v ∈ A then k else (B v).card

def constraintCost {V Color : Type} [DecidableEq V] (S : Finset V)
    (k : ℕ) (A : Finset V) (B : V → Finset Color) : ℕ :=
  ∑ v ∈ S, vertexCost k A B v

lemma constraintCost_eq {V Color : Type} [DecidableEq V] (S A : Finset V)
    (k : ℕ) (B : V → Finset Color) (hAS : A ⊆ S) :
    constraintCost S k A B = k * A.card + ∑ v ∈ S \ A, (B v).card := by
  classical
  have hA : ∑ v ∈ A, vertexCost k A B v = k * A.card := by
    calc
      _ = ∑ _v ∈ A, k := Finset.sum_congr rfl (fun v hv => by simp [vertexCost, hv])
      _ = _ := by simp [Nat.mul_comm]
  have hB : ∑ v ∈ S \ A, vertexCost k A B v = ∑ v ∈ S \ A, (B v).card := by
    apply Finset.sum_congr rfl
    intro v hv
    simp [vertexCost, (Finset.mem_sdiff.mp hv).2]
  unfold constraintCost
  rw [← Finset.sum_sdiff hAS, hA, hB, Nat.add_comm]

lemma constraintCost_card_bound {V Color : Type} [DecidableEq V]
    {S A : Finset V} {k : ℕ} {B : V → Finset Color} (hk : 1 ≤ k)
    (hAS : A ⊆ S) (hbudget : constraintCost S k A B ≤ 2 * k ^ 2) :
    A.card ≤ 2 * k := by
  rw [constraintCost_eq S A k B hAS] at hbudget
  apply Nat.le_of_mul_le_mul_left (c := k) _ hk
  calc
    k * A.card ≤ 2 * k ^ 2 := (Nat.le_add_right _ _).trans hbudget
    _ = k * (2 * k) := by ring

lemma constraintCost_mono {V Color : Type} [DecidableEq V] {S T : Finset V}
    (k : ℕ) (A : Finset V) (B : V → Finset Color) (hTS : T ⊆ S) :
    constraintCost T k A B ≤ constraintCost S k A B :=
  Finset.sum_le_sum_of_subset hTS

lemma promote_constraints {V Color : Type} [DecidableEq V]
    (G : SimpleGraph V) (S A : Finset V) (L B : V → Finset Color)
    (φ : V → Color) {k m : ℕ} (hk : 1 ≤ k) (hAS : A ⊆ S)
    (hL : ∀ v ∈ S, m + 6 * k ≤ (L v).card)
    (hφ : ValidOn G A L φ)
    (hB : ∀ v ∈ S \ A, (B v).card < 3 * k)
    (hbudget : constraintCost S k A B ≤ 2 * k ^ 2) :
    ∃ A' φ', A ⊆ A' ∧ A' ⊆ S ∧ ValidOn G A' L φ' ∧
      (∀ v ∈ A, φ' v = φ v) ∧ (∀ v ∈ A' \ A, φ' v ∉ B v) ∧
      (∀ v ∈ S \ A', (B v).card < k) ∧
      constraintCost S k A' B ≤ constraintCost S k A B := by
  classical
  let A' := A ∪ S.filter (fun v => k ≤ (B v).card)
  have hAA' : A ⊆ A' := Finset.subset_union_left
  have hA'S : A' ⊆ S := Finset.union_subset hAS (Finset.filter_subset _ _)
  have hcost : constraintCost S k A' B ≤ constraintCost S k A B := by
    apply Finset.sum_le_sum
    intro v hv
    by_cases ha : v ∈ A
    · simp [vertexCost, ha, hAA' ha]
    · by_cases ha' : v ∈ A'
      · have hh : k ≤ (B v).card := by
          rcases Finset.mem_union.mp ha' with hh | hh
          · exact (ha hh).elim
          · exact (Finset.mem_filter.mp hh).2
        simpa [vertexCost, ha, ha'] using hh
      · simp [vertexCost, ha, ha']
  have hcard : A'.card ≤ 2 * k := constraintCost_card_bound hk hA'S (hcost.trans hbudget)
  have hchoose : Choosable (G.induce (↑(A' \ A) : Set V)) (A' \ A).card := by
    have hc := choosable_card (G.induce (↑(A' \ A) : Set V))
    change Choosable _ (Fintype.card ↥(A' \ A)) at hc
    rw [Fintype.card_coe] at hc
    exact hc
  have hsizes : ∀ v ∈ A' \ A, (A' \ A).card + (B v).card + A.card ≤ (L v).card := by
    intro v hv
    have hvA' := (Finset.mem_sdiff.mp hv).1
    have hh := hB v (Finset.mem_sdiff.mpr ⟨hA'S hvA', (Finset.mem_sdiff.mp hv).2⟩)
    have hl := hL v (hA'S hvA')
    have heq := Finset.card_sdiff_add_card_eq_card hAA'
    omega
  obtain ⟨φ', hφ', hagree, havoid⟩ :=
    extend_from_choosable G A' A L B φ hφ hchoose hsizes
  refine ⟨A', φ', hAA', hA'S, hφ', hagree, havoid, ?_, hcost⟩
  intro v hv
  have hvS := (Finset.mem_sdiff.mp hv).1
  have hn := (Finset.mem_sdiff.mp hv).2
  by_contra h
  apply hn
  exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hvS, by omega⟩)

lemma choosable_of_iso {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) {k : ℕ} (h : Choosable H k) : Choosable G k := by
  intro Color L hL
  obtain ⟨c, hc, hp⟩ := h Color (fun w => L (e.symm w)) (fun w => hL (e.symm w))
  refine ⟨fun v => c (e v), ?_, ?_⟩
  · intro v
    simpa using hc (e v)
  · intro v w hvw
    exact hp (e.map_adj_iff.mpr hvw)

lemma choosable_of_embedding {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ↪g H) {k : ℕ} (h : Choosable H k) : Choosable G k :=
  choosable_of_iso e.isoInduceRange (choosable_induce h _)

lemma choosable_induce_subset {V : Type} {G : SimpleGraph V} {S T : Set V}
    {k : ℕ} (h : Choosable (G.induce S) k) (hTS : T ⊆ S) :
    Choosable (G.induce T) k :=
  choosable_of_embedding (G.induceHomOfLE hTS) h

end LinearListHadwiger

end OAI
