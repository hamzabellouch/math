import OAI.Combinatorics.ListHadwiger.ConnectivityTests

namespace OAI

namespace LinearListHadwiger

lemma exists_rotation_few_conflicts {V : Type} [DecidableEq V]
    (S : Finset V) {n k : ℕ} (hn : k ≤ n) (hk : 0 < k)
    (d : V → Fin n) (R : Fin n ↪ Fin n) (B : V → Finset (Fin n))
    (hbudget : ∑ v ∈ S, (B v).card ≤ 2 * k ^ 2) :
    ∃ j : Fin n, (S.filter (fun v => R (d v + j) ∈ B v)).card ≤ 2 * k := by
  classical
  have : NeZero n := ⟨by omega⟩
  have hcount (v : V) :
      (Finset.univ.filter (fun j : Fin n => R (d v + j) ∈ B v)).card ≤ (B v).card := by
    apply Finset.card_le_card_of_injOn (fun j : Fin n => R (d v + j))
    · intro j hj
      exact (Finset.mem_filter.mp hj).2
    · intro i hi j hj heq
      exact add_left_cancel (R.injective heq)
  by_contra h
  push Not at h
  have hs : ∑ j : Fin n, (S.filter (fun v => R (d v + j) ∈ B v)).card ≤ 2 * k ^ 2 := by
    calc
      _ = ∑ v ∈ S, (Finset.univ.filter (fun j : Fin n => R (d v + j) ∈ B v)).card := by
        simp only [Finset.card_filter]
        exact Finset.sum_comm
      _ ≤ ∑ v ∈ S, (B v).card := Finset.sum_le_sum (fun v _ => hcount v)
      _ ≤ _ := hbudget
  have hnpos : 0 < n := by omega
  have : Nonempty (Fin n) := ⟨⟨0, hnpos⟩⟩
  have ht := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun j (_ : j ∈ Finset.univ) => h j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at ht
  have hm : 2 * k ^ 2 ≤ n * (2 * k) := by nlinarith
  omega

lemma extend_from_ordinary {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (S A : Finset V) {k m : ℕ}
    (B : V → Finset (Fin (m + 6 * k))) (φ : V → Fin (m + 6 * k))
    (hk : 1 ≤ k) (hAS : A ⊆ S)
    (hcolor : (G.induce (↑S : Set V)).Colorable m)
    (hφ : ValidOn G A (fun _ => Finset.univ) φ)
    (hB : ∀ v ∈ S \ A, (B v).card < k)
    (hbudget : constraintCost S k A B ≤ 2 * k ^ 2) :
    ∃ c, ValidOn G S (fun _ => Finset.univ) c ∧ (∀ v ∈ A, c v = φ v) ∧
      ∀ v ∈ S \ A, c v ∉ B v := by
  classical
  obtain ⟨d₀⟩ := hcolor
  by_cases hS : S = ∅
  · subst S
    have hA : A = ∅ := Finset.subset_empty.mp hAS
    subst A
    exact ⟨φ, ⟨by simp, by simp [ProperOn]⟩, by simp, by simp⟩
  have hmc : 0 < m := by
    obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    exact (d₀ ⟨v, hv⟩).pos
  have hAc := constraintCost_card_bound hk hAS hbudget
  let P : Finset (Fin (m + 6 * k)) := Finset.univ \ A.image φ
  have hPc : m + 4 * k ≤ P.card := by
    have hc := Finset.card_image_le (f := φ) (s := A)
    have hd : (Finset.univ : Finset (Fin (m + 6 * k))).card ≤
        P.card + (A.image φ).card := Finset.card_le_card_sdiff_add_card
    simp only [Finset.card_univ, Fintype.card_fin] at hd
    omega
  have : NeZero P.card := ⟨by omega⟩
  have : NeZero m := ⟨by omega⟩
  let e : Fin P.card ≃ ↥P := (Finset.equivFin P).symm
  let d : V → Fin m := fun v => if hv : v ∈ S then d₀ ⟨v, hv⟩ else 0
  let f : V → Fin P.card := fun v => Fin.castLE (by omega : m ≤ P.card) (d v)
  let B' : V → Finset (Fin P.card) := fun v =>
    Finset.univ.filter (fun j => (e j).val ∈ B v)
  have hB' (v : V) : (B' v).card ≤ (B v).card := by
    apply Finset.card_le_card_of_injOn (fun i => (e i).val)
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
    · intro i hi j hj heq
      exact e.injective (Subtype.ext heq)
  have hsum : ∑ v ∈ S \ A, (B' v).card ≤ 2 * k ^ 2 := by
    have hh := hbudget
    rw [constraintCost_eq S A k B hAS] at hh
    exact (Finset.sum_le_sum (fun v _ => hB' v)).trans (by omega)
  obtain ⟨j, hj⟩ := exists_rotation_few_conflicts (S \ A) (by omega : k ≤ P.card)
    (by omega : 0 < k) f (Function.Embedding.refl _) B' hsum
  let c₀ : V → Fin (m + 6 * k) := fun v => (e (f v + j)).val
  let D := (S \ A).filter (fun v => c₀ v ∈ B v)
  have hDc : D.card ≤ 2 * k := by simpa [D, c₀, B'] using hj
  have hDS : D ⊆ S \ A := Finset.filter_subset _ _
  have hc₀A (v : V) : c₀ v ∉ A.image φ := (Finset.mem_sdiff.mp (e (f v + j)).property).2
  have hc₀proper : ProperOn G S c₀ := by
    intro v hv w hw hadj heq
    have he : f v + j = f w + j := e.injective (Subtype.ext heq)
    have hf : d v = d w := Fin.castLE_injective _ (add_right_cancel he)
    have hvw := d₀.valid (show (G.induce (↑S : Set V)).Adj ⟨v,hv⟩ ⟨w,hw⟩ from hadj)
    apply hvw
    simpa [d, hv, hw] using hf
  have hc₀card : (S.image c₀).card ≤ m := by
    let g : Fin m → Fin (m + 6 * k) := fun a => (e (Fin.castLE (by omega) a + j)).val
    have hsub : S.image c₀ ⊆ Finset.univ.image g := by
      intro a ha
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_image.mpr ⟨d v, Finset.mem_univ _, rfl⟩
    exact (Finset.card_le_card hsub).trans (by simpa using (Finset.card_image_le (s := Finset.univ) (f := g)))
  let L' : (↑D : Set V) → Finset (Fin (m + 6 * k)) := fun v =>
    Finset.univ \ (S.image c₀ ∪ A.image φ ∪ B v)
  have hL' : ∀ v, D.card ≤ (L' v).card := by
    intro v
    have hb := hB v (hDS v.property)
    have hu₁ := Finset.card_union_le (S.image c₀) (A.image φ)
    have hu₂ := Finset.card_union_le (S.image c₀ ∪ A.image φ) (B v)
    have ha := Finset.card_image_le (s := A) (f := φ)
    have hd : (Finset.univ : Finset (Fin (m + 6 * k))).card ≤
        (L' v).card + (S.image c₀ ∪ A.image φ ∪ B v).card := Finset.card_le_card_sdiff_add_card
    simp only [Finset.card_univ, Fintype.card_fin] at hd
    omega
  have q := choosable_card (G.induce (↑D : Set V))
  rw [show Fintype.card (↑D : Set V) = D.card from Fintype.card_coe D] at q
  obtain ⟨cD, hcD, hpD⟩ := q _ L' hL'
  let c : V → Fin (m + 6 * k) := fun v => if hv : v ∈ D then cD ⟨v,hv⟩ else
    if v ∈ A then φ v else c₀ v
  have hDcA : Disjoint D A := Finset.disjoint_left.mpr (fun v hv ha => (Finset.mem_sdiff.mp (hDS hv)).2 ha)
  have hDavoid (v : V) (hv : v ∈ D) :
      c v ∉ S.image c₀ ∧ c v ∉ A.image φ ∧ c v ∉ B v := by
    have hh := hcD ⟨v,hv⟩
    simpa only [L', Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union,
      not_or, and_assoc, c, dite_eq_left hv] using hh
  have hcA : ∀ v ∈ A, c v = φ v := by
    intro v hv
    simp [c, Finset.disjoint_right.mp hDcA hv, hv]
  have hcN (v : V) (hvD : v ∉ D) (hvA : v ∉ A) : c v = c₀ v := by simp [c,hvD,hvA]
  refine ⟨c, ⟨by simp, ?_⟩, hcA, ?_⟩
  · intro v hv w hw hadj
    by_cases hvD : v ∈ D <;> by_cases hwD : w ∈ D
    · simpa only [c, dite_eq_left hvD, dite_eq_left hwD] using
        hpD (v := ⟨v,hvD⟩) (w := ⟨w,hwD⟩) hadj
    · by_cases hwA : w ∈ A
      · rw [hcA w hwA]
        exact fun heq => (hDavoid v hvD).2.1 (heq ▸ Finset.mem_image.mpr ⟨w,hwA,rfl⟩)
      · rw [hcN w hwD hwA]
        intro heq
        apply (hDavoid v hvD).1
        rw [heq]
        exact Finset.mem_image.mpr ⟨w,hw,rfl⟩
    · by_cases hvA : v ∈ A
      · rw [hcA v hvA]
        intro heq
        apply (hDavoid w hwD).2.1
        rw [←heq]
        exact Finset.mem_image.mpr ⟨v,hvA,rfl⟩
      · rw [hcN v hvD hvA]
        intro heq
        apply (hDavoid w hwD).1
        rw [←heq]
        exact Finset.mem_image.mpr ⟨v,hv,rfl⟩
    · by_cases hvA : v ∈ A <;> by_cases hwA : w ∈ A
      · rw [hcA v hvA, hcA w hwA]
        exact hφ.2 hvA hwA hadj
      · rw [hcA v hvA, hcN w hwD hwA]
        intro heq
        apply hc₀A w
        rw [←heq]
        exact Finset.mem_image.mpr ⟨v,hvA,rfl⟩
      · rw [hcN v hvD hvA, hcA w hwA]
        intro heq
        apply hc₀A v
        rw [heq]
        exact Finset.mem_image.mpr ⟨w,hwA,rfl⟩
      · rw [hcN v hvD hvA, hcN w hwD hwA]
        exact hc₀proper hv hw hadj
  · intro v hv
    by_cases hvD : v ∈ D
    · exact (hDavoid v hvD).2.2
    · rw [hcN v hvD (Finset.mem_sdiff.mp hv).2]
      exact fun hh => hvD (Finset.mem_filter.mpr ⟨hv,hh⟩)

theorem ordinary_constrained_coloring_on {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (S A : Finset V) {k m : ℕ}
    (B : V → Finset (Fin (m + 6 * k))) (φ : V → Fin (m + 6 * k))
    (hk : 1 ≤ k) (hAS : A ⊆ S)
    (hconn : ∀ T ⊆ S, KConnectedOn G T k → (G.induce (↑T : Set V)).Colorable m)
    (hφ : ValidOn G A (fun _ => Finset.univ) φ)
    (hB : ∀ v ∈ S \ A, (B v).card < k)
    (hbudget : constraintCost S k A B ≤ 2 * k ^ 2) :
    ∃ c, ValidOn G S (fun _ => Finset.univ) c ∧ (∀ v ∈ A, c v = φ v) ∧
      ∀ v ∈ S \ A, c v ∉ B v := by
  classical
  let : DecidableEq (Fin (m + 6 * k)) := Classical.decEq _
  let L : V → Finset (Fin (m + 6 * k)) := fun _ => Finset.univ
  have hL (v : V) : m + 6 * k ≤ (L v).card := by simp [L]
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
      have hl := hL v
      have heq := Finset.card_sdiff_add_card_eq_card hAS
      omega
    by_cases hc : KConnectedOn G S k
    · exact extend_from_ordinary G S A B φ hk hAS
        (hconn S Finset.Subset.rfl hc) hφ hB hbudget
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
        (fun v _ => hL v) (hφ.mono Finset.inter_subset_left) hB₁ hbudget₁
    obtain ⟨c₁, hc₁, hc₁ext, hc₁av⟩ :=
      ih (V₁ ∪ Z) hs.left_union_ssubset A₁' B₁ φ₁ hA₁'S₁
        (fun T hT => hconn T (hT.trans hS₁))
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
        (fun T hT => hconn T (hT.trans hS₂))
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

theorem colorable_of_connected_induced {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {k m : ℕ} (hk : 1 ≤ k)
    (hconn : ∀ T : Finset V, KConnectedOn G T k →
      (G.induce (↑T : Set V)).Colorable m) : G.Colorable (m + 6 * k) := by
  classical
  have : NeZero (m + 6 * k) := ⟨by omega⟩
  obtain ⟨c, hc, _, _⟩ := ordinary_constrained_coloring_on G Finset.univ ∅
    (fun _ => ∅) (fun _ => 0) hk (Finset.empty_subset _)
    (fun T _ => hconn T) ⟨by simp, by simp [ProperOn]⟩
    (by intro v hv; simpa using (show 0 < k by omega))
    (by simp [constraintCost, vertexCost])
  exact ⟨SimpleGraph.Coloring.mk c (fun {_ _} h => hc.2 (Finset.mem_univ _) (Finset.mem_univ _) h)⟩

lemma ordinary_chromatic_le_iff {V : Type} [Fintype V] (G : SimpleGraph V) (m : ℕ) :
    G.chromaticNumber.toNat ≤ m ↔ G.Colorable m := by
  constructor
  · exact fun h => SimpleGraph.Colorable.mono h G.colorable_chromaticNumber_of_fintype
  · intro h
    have hh := h.chromaticNumber_le
    exact ENat.toNat_le_of_le_natCast hh

theorem ordinary_connectivity_extraction {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {k : ℕ} (hk : 1 ≤ k)
    (hlarge : 6 * k < G.chromaticNumber.toNat) :
    ∃ T : Finset V, KConnectedOn G T k ∧
      G.chromaticNumber.toNat - 6 * k ≤ (G.induce (↑T : Set V)).chromaticNumber.toNat := by
  classical
  by_contra hn
  push Not at hn
  let m := G.chromaticNumber.toNat - 6 * k - 1
  have hconn : ∀ T : Finset V, KConnectedOn G T k →
      (G.induce (↑T : Set V)).Colorable m := by
    intro T hT
    apply (ordinary_chromatic_le_iff _ _).mp
    have hh := hn T hT
    dsimp [m]
    omega
  have hcolor := colorable_of_connected_induced G hk hconn
  have hbound := (ordinary_chromatic_le_iff G _).mpr hcolor
  dsimp [m] at hbound
  omega

open SimpleGraph

structure WeavingWithin {V : Type} (G : SimpleGraph V) (J : Set V)
    {a p : ℕ} (roots : Fin a → V) (x y : Fin p → V) where
  model : RootedCliqueModel G roots
  branch_subset : ∀ j, model.branch j ⊆ J
  paths : ∀ i, G.Path (x i) (y i)
  path_subset : ∀ i v, v ∈ (paths i).val.support → v ∈ J
  disjoint : ∀ i j, i ≠ j → Disjoint
    {v | v ∈ (paths i).val.support} {v | v ∈ (paths j).val.support}
  clean : ∀ i j v, v ∈ (paths i).val.support → v ∈ model.branch j →
    v ∈ Set.range roots ∧ (v = x i ∨ v = y i)

def WovenOn {V : Type} (G : SimpleGraph V) (J : Set V) (a b : ℕ) : Prop :=
  ∀ (roots : Fin a → V), Function.Injective roots → (∀ i, roots i ∈ J) →
    ∀ p ≤ b, ∀ x y : Fin p → V,
      (∀ i, x i ∈ J ∧ y i ∈ J) →
      (∀ i j, i ≠ j → Disjoint ({x i, y i} : Set V) {x j, y j}) →
      Nonempty (WeavingWithin G J roots x y)

def Woven {V : Type} (G : SimpleGraph V) (a b : ℕ) : Prop :=
  WovenOn G Set.univ a b

structure DistrictVisits {V : Type} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (J : Set V) where
  entry : V
  exit : V
  entry_mem : entry ∈ J
  exit_mem : exit ∈ J
  initial : G.Walk u entry
  terminal : G.Walk exit v
  initial_part : ∃ q : G.Walk entry v, p = initial.append q
  terminal_part : ∃ q : G.Walk u exit, p = q.append terminal
  first : ∀ z, z ∈ initial.support → z ∈ J → z = entry
  last : ∀ z, z ∈ terminal.support → z ∈ J → z = exit

lemma first_district_visit {V : Type} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (J : Set V) (h : ∃ z ∈ p.support, z ∈ J) :
    ∃ x ∈ J, ∃ q : G.Walk u x, ∃ r : G.Walk x v,
      p = q.append r ∧ ∀ z, z ∈ q.support → z ∈ J → z = x := by
  classical
  induction p with
  | @nil u =>
    obtain ⟨z,hz,hzJ⟩ := h
    have heq : z = u := by simpa using hz
    subst z
    exact ⟨u,hzJ,.nil,.nil,rfl,by intro z hz _; simpa using hz⟩
  | @cons u v w huv p ih =>
    by_cases hu : u ∈ J
    · exact ⟨u,hu,.nil,.cons huv p,rfl,by intro z hz _; simpa using hz⟩
    · have ht : ∃ z ∈ p.support, z ∈ J := by
        obtain ⟨z,hz,hzJ⟩ := h
        rcases (show z = u ∨ z ∈ p.support by simpa using hz) with rfl | hz
        · exact (hu hzJ).elim
        · exact ⟨z,hz,hzJ⟩
      obtain ⟨x,hx,q,r,hp,hfirst⟩ := ih ht
      refine ⟨x,hx,.cons huv q,r,?_,?_⟩
      · simp only [Walk.cons_append, hp]
      · intro z hz hzJ
        rcases (show z = u ∨ z ∈ q.support by simpa using hz) with rfl | hz
        · exact (hu hzJ).elim
        · exact hfirst z hz hzJ

lemma district_visits_exist {V : Type} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (J : Set V) (h : ∃ z ∈ p.support, z ∈ J) :
    Nonempty (DistrictVisits p J) := by
  obtain ⟨x,hx,q,r,hp,hfirst⟩ := first_district_visit p J h
  have hr : ∃ z ∈ p.reverse.support, z ∈ J := by simpa using h
  obtain ⟨y,hy,q',r',hp',hfirst'⟩ := first_district_visit p.reverse J hr
  refine ⟨⟨x,y,hx,hy,q,q'.reverse,⟨r,hp⟩,?_,hfirst,?_⟩⟩
  · refine ⟨r'.reverse, ?_⟩
    have hh := congrArg Walk.reverse hp'
    simpa only [Walk.reverse_reverse, Walk.reverse_append] using hh
  · intro z hz hzJ
    exact hfirst' z (by simpa using hz) hzJ

namespace DistrictVisits
variable {V : Type} {G : SimpleGraph V} {u v : V} {p : G.Walk u v} {J : Set V}
lemma initial_subset (D : DistrictVisits p J) : D.initial.support ⊆ p.support := by
  obtain ⟨q,hq⟩ := D.initial_part
  simpa only [← hq] using (Walk.support_subset_support_append_left D.initial q)
lemma terminal_subset (D : DistrictVisits p J) : D.terminal.support ⊆ p.support := by
  obtain ⟨q,hq⟩ := D.terminal_part
  simpa only [← hq] using (Walk.support_subset_support_append_right q D.terminal)
lemma entry_on (D : DistrictVisits p J) : D.entry ∈ p.support :=
  D.initial_subset (Walk.end_mem_support _)
lemma exit_on (D : DistrictVisits p J) : D.exit ∈ p.support :=
  D.terminal_subset (Walk.start_mem_support _)
end DistrictVisits

theorem reroute_woven_district {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (J : Set V) {a b q : ℕ} (hJ : WovenOn G J a b)
    (roots : Fin a → V) (hinj : Function.Injective roots) (hr : ∀ i, roots i ∈ J)
    (x y : Fin q → V) (P : ∀ i, G.Path (x i) (y i)) (hq : q ≤ b)
    (hdisj : ∀ i j, i ≠ j → Disjoint
      {v | v ∈ (P i).val.support} {v | v ∈ (P j).val.support}) :
    ∃ M : RootedCliqueModel G roots, (∀ j, M.branch j ⊆ J) ∧
    ∃ P' : ∀ i, G.Path (x i) (y i),
      (∀ i j, i ≠ j → Disjoint
        {v | v ∈ (P' i).val.support} {v | v ∈ (P' j).val.support}) ∧
      (∀ i, (¬∃ z ∈ (P i).val.support, z ∈ J) → P' i = P i) ∧
      (∀ i v, v ∈ (P' i).val.support → v ∉ J → v ∈ (P i).val.support) ∧
      (∀ i j v, v ∈ (P' i).val.support → v ∈ M.branch j →
        v ∈ Set.range roots ∧ ∃ D : DistrictVisits (P i).val J,
          v = D.entry ∨ v = D.exit) := by
  classical
  let I : Type := {i : Fin q // ∃ z ∈ (P i).val.support, z ∈ J}
  have : Fintype I := Fintype.ofFinite _
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let D : ∀ i : I, DistrictVisits (P i.val).val J := fun i =>
    Classical.choice (district_visits_exist (P i.val).val J i.property)
  let s : Fin (Fintype.card I) → V := fun i => (D (e i)).entry
  let t : Fin (Fintype.card I) → V := fun i => (D (e i)).exit
  have hcard : Fintype.card I ≤ b := by
    calc
      Fintype.card I ≤ Fintype.card (Fin q) := Fintype.card_subtype_le _
      _ = q := Fintype.card_fin _
      _ ≤ b := hq
  have hst : ∀ i j, i ≠ j → Disjoint ({s i,t i} : Set V) {s j,t j} := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro v hvi hvj
    have hi : v ∈ (P (e i).val).val.support := by
      rcases hvi with rfl | hv
      · exact (D (e i)).entry_on
      · have heq : v = t i := hv
        rw [heq]
        exact (D (e i)).exit_on
    have hj : v ∈ (P (e j).val).val.support := by
      rcases hvj with rfl | hv
      · exact (D (e j)).entry_on
      · have heq : v = t j := hv
        rw [heq]
        exact (D (e j)).exit_on
    exact Set.disjoint_left.mp (hdisj _ _ (fun h => hij (e.injective (Subtype.ext h)))) hi hj
  obtain ⟨W⟩ := hJ roots hinj hr (Fintype.card I) hcard s t
    (fun i => ⟨(D (e i)).entry_mem,(D (e i)).exit_mem⟩) hst
  have hs (i : I) : s (e.symm i) = (D i).entry :=
    congrArg (fun j : I => (D j).entry) (e.apply_symm_apply i)
  have ht (i : I) : t (e.symm i) = (D i).exit :=
    congrArg (fun j : I => (D j).exit) (e.apply_symm_apply i)
  let Q : ∀ i : I, G.Path (D i).entry (D i).exit := fun i =>
    ⟨(W.paths (e.symm i)).val.copy (hs i) (ht i), by
      simp⟩
  have hQsup (i : I) (v : V) :
      v ∈ (Q i).val.support ↔ v ∈ (W.paths (e.symm i)).val.support := by
    simp [Q]
  let P' : ∀ i, G.Path (x i) (y i) := fun i =>
    if hi : ∃ z ∈ (P i).val.support, z ∈ J then
      (((D ⟨i,hi⟩).initial.append (Q ⟨i,hi⟩).val).append (D ⟨i,hi⟩).terminal).toPath
    else P i
  have hparts (i : Fin q) (hi : ∃ z ∈ (P i).val.support, z ∈ J) (v : V)
      (hv : v ∈ (P' i).val.support) :
      v ∈ (D ⟨i,hi⟩).initial.support ∨ v ∈ (Q ⟨i,hi⟩).val.support ∨
        v ∈ (D ⟨i,hi⟩).terminal.support := by
    simp only [P',dite_eq_left hi] at hv
    have hh := Walk.support_toPath_subset_support _ hv
    simpa only [Walk.mem_support_append_iff, or_assoc] using hh
  have houtside (i : Fin q) (v : V) (hv : v ∈ (P' i).val.support) (hn : v ∉ J) :
      v ∈ (P i).val.support := by
    by_cases hi : ∃ z ∈ (P i).val.support, z ∈ J
    · rcases hparts i hi v hv with hpre | hrep | hsuf
      · exact (D ⟨i,hi⟩).initial_subset hpre
      · exact (hn (W.path_subset _ v ((hQsup _ _).mp hrep))).elim
      · exact (D ⟨i,hi⟩).terminal_subset hsuf
    · simpa only [P',dite_eq_right hi] using hv
  have hinside (i : Fin q) (v : V) (hv : v ∈ (P' i).val.support) (hvJ : v ∈ J) :
      ∃ hi : ∃ z ∈ (P i).val.support, z ∈ J, v ∈ (Q ⟨i,hi⟩).val.support := by
    by_cases hi : ∃ z ∈ (P i).val.support, z ∈ J
    · refine ⟨hi,?_⟩
      rcases hparts i hi v hv with hpre | hrep | hsuf
      · rw [(D ⟨i,hi⟩).first v hpre hvJ]
        exact Walk.start_mem_support _
      · exact hrep
      · rw [(D ⟨i,hi⟩).last v hsuf hvJ]
        exact Walk.end_mem_support _
    · exact (hi ⟨v,by simpa only [P',dite_eq_right hi] using hv,hvJ⟩).elim
  refine ⟨W.model,W.branch_subset,P',?_,?_,houtside,?_⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro v hvi hvj
    by_cases hvJ : v ∈ J
    · obtain ⟨hi,hQi⟩ := hinside i v hvi hvJ
      obtain ⟨hj,hQj⟩ := hinside j v hvj hvJ
      have hne : e.symm ⟨i,hi⟩ ≠ e.symm ⟨j,hj⟩ := by
        intro h
        exact hij (congrArg Subtype.val (e.symm.injective h))
      exact Set.disjoint_left.mp (W.disjoint _ _ hne) ((hQsup _ _).mp hQi) ((hQsup _ _).mp hQj)
    · exact Set.disjoint_left.mp (hdisj i j hij) (houtside i v hvi hvJ) (houtside j v hvj hvJ)
  · intro i hi
    simp only [P',dite_eq_right hi]
  · intro i j v hv hm
    obtain ⟨hi,hQi⟩ := hinside i v hv (W.branch_subset j hm)
    have hc := W.clean (e.symm ⟨i,hi⟩) j v ((hQsup _ _).mp hQi) hm
    refine ⟨hc.1,D ⟨i,hi⟩,?_⟩
    simpa only [hs,ht] using hc.2

end LinearListHadwiger

end OAI
