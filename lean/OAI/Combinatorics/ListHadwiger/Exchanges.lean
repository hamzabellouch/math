import OAI.Combinatorics.ListHadwiger.BagContraction

namespace OAI

namespace LinearListHadwiger
open SimpleGraph PathPacking
open scoped Classical

namespace BagRouting
variable {V I J : Type} {G : SimpleGraph V} {s : I → V} {B : J → Set V}

def used (D : BagRouting G s B) : Set V :=
  {v | ∃ i, v ∈ (D.paths i).2.val.support}

def Minimal [Fintype I] (D : BagRouting G s B) : Prop :=
  ∀ E : BagRouting G s B, D.totalLength ≤ E.totalLength

lemma exists_minimal [Fintype I] (h : Nonempty (BagRouting G s B)) :
    ∃ D : BagRouting G s B, D.Minimal := by
  classical
  have hex : ∃ n : ℕ, ∃ D : BagRouting G s B, D.totalLength = n := by
    obtain ⟨D⟩ := h
    exact ⟨D.totalLength, D, rfl⟩
  obtain ⟨D, hd⟩ := Nat.find_spec hex
  refine ⟨D, fun E => ?_⟩
  rw [hd]
  exact Nat.find_min' hex ⟨E, rfl⟩

noncomputable def replace [DecidableEq I] (D : BagRouting G s B) (i : I)
    (p : G.Path (s i) (D.paths i).1)
    (hp : ∀ j, i ≠ j → ∀ v ∈ p.val.support,
      v ∈ (D.paths j).2.val.support → v = s i ∧ v = s j) : BagRouting G s B := by
  let paths : ∀ a, Σ w, G.Path (s a) w :=
    fun a => if h : a = i then h.symm ▸ (⟨(D.paths i).1, p⟩ : Σ w, G.Path (s i) w) else D.paths a
  refine ⟨paths, D.bag, D.bag_injective, ?_, ?_⟩
  · intro a
    by_cases ha : a = i
    · subst a
      have he : paths i = ⟨(D.paths i).1, p⟩ := dite_eq_left rfl
      rw [he]
      exact D.endpoint_mem i
    · have he : paths a = D.paths a := dite_eq_right ha
      rw [he]
      exact D.endpoint_mem a
  · intro a b hab v hva hvb
    by_cases ha : a = i
    · subst a
      have he : paths i = ⟨(D.paths i).1, p⟩ := dite_eq_left rfl
      have he' : paths b = D.paths b := dite_eq_right (Ne.symm hab)
      rw [he] at hva
      rw [he'] at hvb
      exact hp b hab v hva hvb
    · have he : paths a = D.paths a := dite_eq_right ha
      rw [he] at hva
      by_cases hb : b = i
      · subst b
        have he' : paths i = ⟨(D.paths i).1, p⟩ := dite_eq_left rfl
        rw [he'] at hvb
        exact (hp a (Ne.symm ha) v hvb hva).symm
      · have he' : paths b = D.paths b := dite_eq_right hb
        rw [he'] at hvb
        exact D.overlap a b hab v hva hvb

lemma replace_shorter [Fintype I] [DecidableEq I] (D : BagRouting G s B) (i : I)
    (p : G.Path (s i) (D.paths i).1)
    (hp : ∀ j, i ≠ j → ∀ v ∈ p.val.support,
      v ∈ (D.paths j).2.val.support → v = s i ∧ v = s j)
    (hlt : p.val.length < (D.paths i).2.val.length) :
    (D.replace i p hp).totalLength < D.totalLength := by
  have hi : (D.replace i p hp).paths i = ⟨(D.paths i).1, p⟩ := dite_eq_left rfl
  have ha : ∀ a, a ≠ i → (D.replace i p hp).paths a = D.paths a := fun a h => dite_eq_right h
  apply Finset.sum_lt_sum
  · intro a _
    by_cases h : a = i
    · subst a
      rw [hi]
      exact hlt.le
    · rw [ha a h]
  · refine ⟨i, Finset.mem_univ _, ?_⟩
    rw [hi]
    exact hlt

lemma Minimal.walk_length_le [Fintype I] [DecidableEq V] [DecidableEq I]
    {D : BagRouting G s B} (hD : D.Minimal) (i : I)
    (p : G.Walk (s i) (D.paths i).1)
    (hp : ∀ j, i ≠ j → ∀ v ∈ p.support,
      v ∈ (D.paths j).2.val.support → v = s i ∧ v = s j) :
    (D.paths i).2.val.length ≤ p.length := by
  have hp' : ∀ j, i ≠ j → ∀ v ∈ p.toPath.val.support,
      v ∈ (D.paths j).2.val.support → v = s i ∧ v = s j := by
    intro j hij v hv hvj
    exact hp j hij v (p.support_toPath_subset_support hv) hvj
  have hle : (D.paths i).2.val.length ≤ p.toPath.val.length := by
    by_contra hn
    exact (not_lt_of_ge (hD (D.replace i p.toPath hp')))
      (D.replace_shorter i p.toPath hp' (Nat.lt_of_not_ge hn))
  exact hle.trans p.length_bypass_le_length

lemma Minimal.no_long_shortcut [Fintype I] [DecidableEq V] [DecidableEq I]
    {D : BagRouting G s B} (hD : D.Minimal) (i : I) (v : V) (hv : v ∉ D.used)
    (a b : ℕ) (ha : a ≤ (D.paths i).2.val.length) (hb : b ≤ (D.paths i).2.val.length)
    (hva : G.Adj ((D.paths i).2.val.getVert a) v)
    (hvb : G.Adj v ((D.paths i).2.val.getVert b)) : b ≤ a + 2 := by
  let p := (D.paths i).2.val
  let q : G.Walk (s i) (D.paths i).1 := ((p.take a).concat hva).append (Walk.cons hvb (p.drop b))
  change a ≤ p.length at ha
  change b ≤ p.length at hb
  have hq := hD.walk_length_le i q (by
    intro j hij w hw hwj
    have hw' : w ∈ p.support ∨ w = v := by
      simp only [q, Walk.mem_support_append_iff, Walk.support_concat, Walk.support_cons,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with (hw | hw) | (hw | hw)
      · left
        rw [Walk.support_take] at hw
        exact List.mem_of_mem_take hw
      · exact Or.inr hw
      · exact Or.inr hw
      · left
        rw [Walk.drop_support_eq_support_drop_min] at hw
        exact List.mem_of_mem_drop hw
    rcases hw' with hw | rfl
    · exact D.overlap i j hij w hw hwj
    · exact (hv ⟨j, hwj⟩).elim)
  have hlen : q.length = a + 2 + (p.length - b) := by
    simp [q, Walk.take_length, Nat.min_eq_left ha, Walk.drop_length]
    omega
  change p.length ≤ q.length at hq
  rw [hlen] at hq
  omega

lemma Minimal.path_neighbors_le_three [Fintype I] [DecidableEq V] [DecidableEq I]
    [DecidableRel G.Adj]
    {D : BagRouting G s B} (hD : D.Minimal) (i : I) (v : V) (hv : v ∉ D.used) :
    ((D.paths i).2.val.support.toFinset.filter fun w => G.Adj v w).card ≤ 3 := by
  classical
  let p := (D.paths i).2.val
  let R := (Finset.range (p.length + 1)).filter fun a => G.Adj v (p.getVert a)
  have hR : R.card ≤ 3 := by
    obtain he | hn := R.eq_empty_or_nonempty
    · simp [he]
    let a := R.min' hn
    have haR : a ∈ R := R.min'_mem hn
    have ha : a ≤ p.length := by
      have hh := (Finset.mem_filter.mp haR).1
      simp only [Finset.mem_range] at hh
      omega
    have hsub : R ⊆ Finset.Icc a (a + 2) := by
      intro b hbR
      have hb : b ≤ p.length := by
        have hh := (Finset.mem_filter.mp hbR).1
        simp only [Finset.mem_range] at hh
        omega
      have hab := hD.no_long_shortcut i v hv a b ha hb
        (Finset.mem_filter.mp haR).2.symm (Finset.mem_filter.mp hbR).2
      exact Finset.mem_Icc.mpr ⟨R.min'_le b hbR, hab⟩
    exact (Finset.card_le_card hsub).trans (by simp; omega)
  have hsub : (p.support.toFinset.filter fun w => G.Adj v w) ⊆ R.image p.getVert := by
    intro w hw
    obtain ⟨hwp, hvw⟩ := Finset.mem_filter.mp hw
    obtain ⟨a, ha, hlen⟩ := Walk.mem_support_iff_exists_getVert.mp (List.mem_toFinset.mp hwp)
    refine Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨?_, ?_⟩, ha⟩
    · exact Finset.mem_range.mpr (by omega)
    · rwa [ha]
  exact (Finset.card_le_card hsub).trans ((Finset.card_image_le).trans hR)

noncomputable def usedFinset [Fintype I] [DecidableEq V] (D : BagRouting G s B) : Finset V :=
  Finset.univ.biUnion fun i => (D.paths i).2.val.support.toFinset

lemma mem_usedFinset [Fintype I] [DecidableEq V] (D : BagRouting G s B) (v : V) :
    v ∈ D.usedFinset ↔ v ∈ D.used := by
  simp [usedFinset, used]

lemma Minimal.used_neighbors_le [Fintype I] [DecidableEq V] [DecidableEq I]
    [DecidableRel G.Adj]
    {D : BagRouting G s B} (hD : D.Minimal) (v : V) (hv : v ∉ D.used) :
    (D.usedFinset.filter fun w => G.Adj v w).card ≤ 3 * Fintype.card I := by
  classical
  have he : D.usedFinset.filter (fun w => G.Adj v w) =
      Finset.univ.biUnion (fun i => (D.paths i).2.val.support.toFinset.filter fun w => G.Adj v w) := by
    ext w
    simp only [Finset.mem_filter, usedFinset, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨i, hi⟩, hw⟩
      exact ⟨i, hi, hw⟩
    · rintro ⟨i, hi, hw⟩
      exact ⟨⟨i, hi⟩, hw⟩
  rw [he]
  calc
    _ ≤ ∑ i : I, ((D.paths i).2.val.support.toFinset.filter fun w => G.Adj v w).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : I, 3 := Finset.sum_le_sum (fun i _ => hD.path_neighbors_le_three i v hv)
    _ = 3 * Fintype.card I := by simp [Nat.mul_comm]

lemma mem_take_indices {u w : V} (p : G.Walk u w) (a : ℕ) {v : V}
    (hv : v ∈ (p.take a).support) :
    ∃ n, n ≤ a ∧ n ≤ p.length ∧ p.getVert n = v := by
  obtain ⟨n, hn, hlen⟩ := Walk.mem_support_iff_exists_getVert.mp hv
  rw [Walk.take_length] at hlen
  have hna := (Nat.le_min.mp hlen).1
  have hnl := (Nat.le_min.mp hlen).2
  rw [Walk.take_getVert, Nat.min_eq_right hna] at hn
  exact ⟨n, hna, hnl, hn⟩

lemma mem_drop_indices {u w : V} (p : G.Walk u w) (b : ℕ) (hb : b ≤ p.length)
    {v : V} (hv : v ∈ (p.drop b).support) :
    ∃ n, b ≤ n ∧ n ≤ p.length ∧ p.getVert n = v := by
  obtain ⟨n, hn, hlen⟩ := Walk.mem_support_iff_exists_getVert.mp hv
  rw [Walk.drop_length] at hlen
  rw [Walk.drop_getVert] at hn
  exact ⟨b + n, by omega, by omega, hn⟩

lemma take_drop_disjoint {u w : V} (p : G.Path u w) (a b : ℕ)
    (hab : a < b) (hb : b ≤ p.val.length) :
    Disjoint {v | v ∈ (p.val.take a).support} {v | v ∈ (p.val.drop b).support} := by
  rw [Set.disjoint_left]
  intro v hv ht
  obtain ⟨c, hca, hcl, hc⟩ := mem_take_indices p.val a hv
  obtain ⟨d, hbd, hdl, hd⟩ := mem_drop_indices p.val b hb ht
  have he := p.property.getVert_injOn hcl hdl (hc.trans hd.symm)
  omega

lemma source_not_mem_drop {u w : V} (p : G.Path u w) (b : ℕ)
    (hpos : 0 < b) (hb : b ≤ p.val.length) : u ∉ (p.val.drop b).support := by
  intro hu
  obtain ⟨n, hbn, hnl, hn⟩ := mem_drop_indices p.val b hb hu
  have h0 : p.val.getVert 0 = u := p.val.getVert_zero
  have he := p.property.getVert_injOn (show 0 ≤ p.val.length by omega) hnl (h0.trans hn.symm)
  omega

structure Exchange (D : BagRouting G s B) where
  active : Finset I
  e : Equiv.Perm I
  fixed : ∀ i, i ∉ active → e i = i
  stable : ∀ i, i ∈ active ↔ e i ∈ active
  a : I → ℕ
  b : I → ℕ
  bounds : ∀ i ∈ active, a i + 2 ≤ b i ∧ b i ≤ (D.paths i).2.val.length
  edge : ∀ i ∈ active,
    G.Adj ((D.paths i).2.val.getVert (a i)) ((D.paths (e i)).2.val.getVert (b (e i)))

namespace Exchange
variable [DecidableEq V] [DecidableEq I] {D : BagRouting G s B}

noncomputable def front (E : D.Exchange) (i : I) : Set V :=
  if i ∈ E.active then {v | v ∈ ((D.paths i).2.val.take (E.a i)).support}
  else {v | v ∈ (D.paths i).2.val.support}

noncomputable def tail (E : D.Exchange) (i : I) : Set V :=
  if i ∈ E.active then {v | v ∈ ((D.paths i).2.val.drop (E.b i)).support} else ∅

lemma front_subset {V I J : Type} {G : SimpleGraph V} {s : I → V} {B : J → Set V}
    [DecidableEq V] [DecidableEq I] {D : BagRouting G s B}
    (E : D.Exchange) (i : I) : E.front i ⊆ {v | v ∈ (D.paths i).2.val.support} := by
  intro v hv
  by_cases hi : i ∈ E.active
  · rw [front, ite_eq_left hi] at hv
    rw [Walk.support_take] at hv
    exact List.mem_of_mem_take hv
  · simpa [front, hi] using hv

lemma tail_subset {V I J : Type} {G : SimpleGraph V} {s : I → V} {B : J → Set V}
    [DecidableEq V] [DecidableEq I] {D : BagRouting G s B}
    (E : D.Exchange) (i : I) : E.tail i ⊆ {v | v ∈ (D.paths i).2.val.support} := by
  intro v hv
  by_cases hi : i ∈ E.active
  · rw [tail, ite_eq_left hi] at hv
    rw [Walk.drop_support_eq_support_drop_min] at hv
    exact List.mem_of_mem_drop hv
  · simp [tail, hi] at hv

lemma not_source_tail {V I J : Type} {G : SimpleGraph V} {s : I → V} {B : J → Set V}
    [DecidableEq V] [DecidableEq I] {D : BagRouting G s B}
    (E : D.Exchange) (i : I) : s i ∉ E.tail i := by
  by_cases hi : i ∈ E.active
  · rw [tail, ite_eq_left hi]
    exact source_not_mem_drop _ _ (by have := (E.bounds i hi).1; omega) (E.bounds i hi).2
  · simp [tail, hi]

lemma front_tail_disjoint {V I J : Type} {G : SimpleGraph V} {s : I → V} {B : J → Set V}
    [DecidableEq V] [DecidableEq I] {D : BagRouting G s B}
    (E : D.Exchange) (i : I) : Disjoint (E.front i) (E.tail i) := by
  by_cases hi : i ∈ E.active
  · rw [front, tail, ite_eq_left hi, ite_eq_left hi]
    exact take_drop_disjoint _ _ _ (by have := (E.bounds i hi).1; omega) (E.bounds i hi).2
  · simp [tail, hi]

noncomputable def walk (E : D.Exchange) (i : I) (hi : i ∈ E.active) :
    G.Walk (s i) (D.paths (E.e i)).1 :=
  (((D.paths i).2.val.take (E.a i)).concat (E.edge i hi)).append
    ((D.paths (E.e i)).2.val.drop (E.b (E.e i)))

lemma walk_support {V I J : Type} {G : SimpleGraph V} {s : I → V} {B : J → Set V}
    [DecidableEq V] [DecidableEq I] {D : BagRouting G s B}
    (E : D.Exchange) (i : I) (hi : i ∈ E.active) {v : V}
    (hv : v ∈ (E.walk i hi).support) : v ∈ E.front i ∪ E.tail (E.e i) := by
  have hei := (E.stable i).mp hi
  rw [front, tail, ite_eq_left hi, ite_eq_left hei]
  simp only [walk, Walk.mem_support_append_iff, Walk.support_concat, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with (hv | hv) | hv
  · exact Or.inl hv
  · subst v
    exact Or.inr (Walk.start_mem_support _)
  · exact Or.inr hv

lemma support_overlap (E : D.Exchange) (i j : I) (hij : i ≠ j) (v : V)
    (hi : v ∈ E.front i ∪ E.tail (E.e i))
    (hj : v ∈ E.front j ∪ E.tail (E.e j)) : v = s i ∧ v = s j := by
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · exact D.overlap i j hij v (E.front_subset i hi) (E.front_subset j hj)
  · by_cases he : i = E.e j
    · subst i
      exact (Set.disjoint_left.mp (E.front_tail_disjoint _) hi hj).elim
    · have h := D.overlap i (E.e j) he v (E.front_subset i hi) (E.tail_subset _ hj)
      exact (E.not_source_tail _ (h.2 ▸ hj)).elim
  · by_cases he : j = E.e i
    · subst j
      exact (Set.disjoint_left.mp (E.front_tail_disjoint _) hj hi).elim
    · have h := D.overlap j (E.e i) he v (E.front_subset j hj) (E.tail_subset _ hi)
      exact (E.not_source_tail _ (h.2 ▸ hi)).elim
  · have he : E.e i ≠ E.e j := fun h => hij (E.e.injective h)
    have h := D.overlap _ _ he v (E.tail_subset _ hi) (E.tail_subset _ hj)
    exact (E.not_source_tail _ (h.1 ▸ hi)).elim

noncomputable def routing (E : D.Exchange) : BagRouting G s B := by
  let paths : ∀ i, Σ v, G.Path (s i) v := fun i =>
    if hi : i ∈ E.active then ⟨(D.paths (E.e i)).1, (E.walk i hi).toPath⟩ else D.paths i
  refine ⟨paths, D.bag ∘ E.e, D.bag_injective.comp E.e.injective, ?_, ?_⟩
  · intro i
    by_cases hi : i ∈ E.active
    · have he : paths i = ⟨(D.paths (E.e i)).1, (E.walk i hi).toPath⟩ := dite_eq_left hi
      rw [he]
      exact D.endpoint_mem _
    · have he : paths i = D.paths i := dite_eq_right hi
      rw [he]
      simpa [E.fixed i hi] using D.endpoint_mem i
  · intro i j hij v hvi hvj
    apply E.support_overlap i j hij v
    · by_cases hi : i ∈ E.active
      · have he : paths i = ⟨(D.paths (E.e i)).1, (E.walk i hi).toPath⟩ := dite_eq_left hi
        rw [he] at hvi
        exact E.walk_support i hi ((E.walk i hi).support_toPath_subset_support hvi)
      · have he : paths i = D.paths i := dite_eq_right hi
        rw [he] at hvi
        exact Or.inl (by simpa [front, hi] using hvi)
    · by_cases hj : j ∈ E.active
      · have he : paths j = ⟨(D.paths (E.e j)).1, (E.walk j hj).toPath⟩ := dite_eq_left hj
        rw [he] at hvj
        exact E.walk_support j hj ((E.walk j hj).support_toPath_subset_support hvj)
      · have he : paths j = D.paths j := dite_eq_right hj
        rw [he] at hvj
        exact Or.inl (by simpa [front, hj] using hvj)

lemma length_inequality (E : D.Exchange) (i : I) :
    (E.routing.paths i).2.val.length + (if E.e i ∈ E.active then E.b (E.e i) else 0) ≤
      (D.paths (E.e i)).2.val.length + (if i ∈ E.active then E.a i + 1 else 0) := by
  by_cases hi : i ∈ E.active
  · have he : E.routing.paths i = ⟨(D.paths (E.e i)).1, (E.walk i hi).toPath⟩ := dite_eq_left hi
    rw [he, ite_eq_left hi, ite_eq_left ((E.stable i).mp hi)]
    have hlen : (E.walk i hi).toPath.val.length ≤ (E.walk i hi).length :=
      (E.walk i hi).length_bypass_le_length
    have ha := (E.bounds i hi).1
    have hb := E.bounds (E.e i) ((E.stable i).mp hi)
    have hia := E.bounds i hi
    have hleni : E.a i ≤ (D.paths i).2.val.length := by omega
    have hwlen : (E.walk i hi).length = E.a i + 1 +
        ((D.paths (E.e i)).2.val.length - E.b (E.e i)) := by
      simp only [walk, Walk.length_append, Walk.length_concat, Walk.take_length,
        Nat.min_eq_left hleni, Walk.drop_length]
    rw [hwlen] at hlen
    change (E.walk i hi).toPath.val.length + E.b (E.e i) ≤ _
    omega
  · have he : E.routing.paths i = D.paths i := dite_eq_right hi
    rw [he, E.fixed i hi]
    simp only [ite_eq_right hi, le_refl]

lemma shorter [Fintype I] (E : D.Exchange) (hE : E.active.Nonempty) :
    E.routing.totalLength < D.totalLength := by
  let a : I → ℕ := fun i => if i ∈ E.active then E.a i + 1 else 0
  let b : I → ℕ := fun i => if i ∈ E.active then E.b i else 0
  have hlt : (∑ i, a i) < ∑ i, b i := by
    apply Finset.sum_lt_sum
    · intro i _
      by_cases hi : i ∈ E.active
      · have := (E.bounds i hi).1
        simp only [a, b, ite_eq_left hi]
        omega
      · simp [a, b, hi]
    · obtain ⟨i, hi⟩ := hE
      refine ⟨i, Finset.mem_univ _, ?_⟩
      have := (E.bounds i hi).1
      simp only [a, b, ite_eq_left hi]
      omega
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => E.length_inequality i)
  change (∑ i, ((E.routing.paths i).2.val.length + b (E.e i))) ≤
    ∑ i, ((D.paths (E.e i)).2.val.length + a i) at hs
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Equiv.sum_comp E.e b,
    Equiv.sum_comp E.e (fun i => (D.paths i).2.val.length)] at hs
  change E.routing.totalLength + (∑ i, b i) ≤ D.totalLength + (∑ i, a i) at hs
  omega

end Exchange

lemma Minimal.no_exchange [Fintype I] [DecidableEq V] [DecidableEq I]
    {D : BagRouting G s B} (hD : D.Minimal) (E : D.Exchange) : ¬ E.active.Nonempty := by
  intro hE
  exact (not_lt_of_ge (hD E.routing)) (E.shorter hE)

lemma cycle_permutation [Fintype I] [DecidableEq I] (Q : Finset I) (hQ : Q.Nonempty)
    (f : I → I) (hf : ∀ i ∈ Q, f i ∈ Q) :
    ∃ T : Finset I, T ⊆ Q ∧ T.Nonempty ∧ ∃ e : Equiv.Perm I,
      (∀ i, i ∉ T → e i = i) ∧ (∀ i, i ∈ T ↔ e i ∈ T) ∧
      (∀ i ∈ T, e i = f i) := by
  classical
  let C := Q.powerset.filter fun T => T.Nonempty ∧ ∀ i ∈ T, f i ∈ T
  have hQC : Q ∈ C := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (by rfl), hQ, hf⟩
  obtain ⟨T, hTC, hmin⟩ := C.exists_min_image Finset.card ⟨Q, hQC⟩
  obtain ⟨hTQ, hn, hclosed⟩ := Finset.mem_filter.mp hTC
  have hsub : T.image f ⊆ T := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact hclosed j hj
  have hIC : T.image f ∈ C := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hsub.trans (Finset.mem_powerset.mp hTQ)),
      hn.image f, ?_⟩
    intro i hi
    exact Finset.mem_image.mpr ⟨i, hsub hi, rfl⟩
  have heq : T.image f = T := Finset.eq_of_subset_of_card_le hsub (hmin _ hIC)
  let g : ↥T → ↥T := fun i => ⟨f i, hclosed i i.property⟩
  have hsurj : Function.Surjective g := by
    intro i
    have hi : i.val ∈ T.image f := heq.symm ▸ i.property
    obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hi
    exact ⟨⟨j, hj⟩, Subtype.ext he⟩
  let e0 : Equiv.Perm ↥T := Equiv.ofBijective g (Finite.surjective_iff_bijective.mp hsurj)
  let e := Equiv.Perm.ofSubtype e0
  refine ⟨T, Finset.mem_powerset.mp hTQ, hn, e, ?_, ?_, ?_⟩
  · intro i hi
    exact Equiv.Perm.ofSubtype_apply_of_not_mem e0 hi
  · intro i
    exact (Equiv.Perm.ofSubtype_apply_mem_iff_mem e0 i).symm
  · intro i hi
    exact Equiv.Perm.ofSubtype_apply_of_mem e0 hi

lemma Minimal.low_degree [Fintype I] [DecidableEq V] [DecidableEq I]
    [DecidableRel G.Adj] {D : BagRouting G s B} (hD : D.Minimal)
    (S : Finset V) (hS : S ⊆ D.usedFinset) (hne : S.Nonempty) :
    ∃ v ∈ S, (S.filter (G.Adj v)).card ≤ 2 * Fintype.card I := by
  classical
  by_contra hno
  have hdeg : ∀ v ∈ S, 2 * Fintype.card I < (S.filter (G.Adj v)).card := by
    intro v hv
    exact Nat.lt_of_not_ge (fun hh => hno ⟨v, hv, hh⟩)
  let R : I → Finset ℕ := fun i => (Finset.range ((D.paths i).2.val.length + 1)).filter
    fun a => (D.paths i).2.val.getVert a ∈ S
  let Q : Finset I := Finset.univ.filter fun i => (R i).Nonempty
  let a : I → ℕ := fun i => if hi : (R i).Nonempty then (R i).min' hi else 0
  have hQiff : ∀ i, i ∈ Q ↔ (R i).Nonempty := by simp [Q]
  have hamin : ∀ i ∈ Q, a i ∈ R i := by
    intro i hi
    have hn := (hQiff i).mp hi
    dsimp [a]
    rw [dite_eq_left hn]
    exact Finset.min'_mem _ _
  have haS : ∀ i ∈ Q, (D.paths i).2.val.getVert (a i) ∈ S := by
    intro i hi
    exact (Finset.mem_filter.mp (hamin i hi)).2
  have hfind : ∀ v ∈ S, ∃ i ∈ Q, ∃ b, b ∈ R i ∧ (D.paths i).2.val.getVert b = v := by
    intro v hv
    obtain ⟨i, hi⟩ := (D.mem_usedFinset v).mp (hS hv)
    obtain ⟨b, hb, hblen⟩ := Walk.mem_support_iff_exists_getVert.mp hi
    have hbR : b ∈ R i := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hb ▸ hv⟩
    exact ⟨i, (hQiff i).mpr ⟨b, hbR⟩, b, hbR, hb⟩
  have hQ : Q.Nonempty := by
    obtain ⟨v, hv⟩ := hne
    obtain ⟨i, hi, _⟩ := hfind v hv
    exact ⟨i, hi⟩
  let M := Finset.univ.biUnion fun i : I =>
    {(D.paths i).2.val.getVert (a i), (D.paths i).2.val.getVert (a i + 1)}
  have hM : M.card ≤ 2 * Fintype.card I := by
    calc
      _ ≤ ∑ i : I, ({(D.paths i).2.val.getVert (a i),
        (D.paths i).2.val.getVert (a i + 1)} : Finset V).card := Finset.card_biUnion_le
      _ ≤ ∑ i : I, 2 := Finset.sum_le_sum fun _ _ => Finset.card_le_two
      _ = _ := by simp [Nat.mul_comm]
  have hm0 : ∀ i, (D.paths i).2.val.getVert (a i) ∈ M := by
    intro i
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simp⟩
  have hm1 : ∀ i, (D.paths i).2.val.getVert (a i + 1) ∈ M := by
    intro i
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simp⟩
  have hout : ∀ i, ∃ j b, i ∈ Q → j ∈ Q ∧ a j + 2 ≤ b ∧
      b ≤ (D.paths j).2.val.length ∧
      G.Adj ((D.paths i).2.val.getVert (a i)) ((D.paths j).2.val.getVert b) := by
    intro i
    by_cases hi : i ∈ Q
    · have hlarge := hdeg _ (haS i hi)
      have hex : ∃ v ∈ S.filter (G.Adj ((D.paths i).2.val.getVert (a i))), v ∉ M := by
        by_contra hh
        have hsub : S.filter (G.Adj ((D.paths i).2.val.getVert (a i))) ⊆ M := by
          intro v hv
          by_contra hvm
          exact hh ⟨v, hv, hvm⟩
        have hle := (Finset.card_le_card hsub).trans hM
        omega
      obtain ⟨v, hv, hvm⟩ := hex
      obtain ⟨hvS, hvadj⟩ := Finset.mem_filter.mp hv
      obtain ⟨j, hj, b, hbR, hb⟩ := hfind v hvS
      have hbj : a j ≤ b := by
        have hn := (hQiff j).mp hj
        dsimp [a]
        rw [dite_eq_left hn]
        exact Finset.min'_le _ _ hbR
      have hb0 : b ≠ a j := by
        intro he
        apply hvm
        rw [he] at hb
        exact hb ▸ hm0 j
      have hb1 : b ≠ a j + 1 := by
        intro he
        apply hvm
        rw [he] at hb
        exact hb ▸ hm1 j
      have hblen : b ≤ (D.paths j).2.val.length := by
        have hh := (Finset.mem_filter.mp hbR).1
        simp only [Finset.mem_range] at hh
        omega
      refine ⟨j, b, fun _ => ⟨hj, by omega, hblen, ?_⟩⟩
      rwa [hb]
    · exact ⟨i, 0, fun hh => (hi hh).elim⟩
  choose f c hfc using hout
  obtain ⟨T, hTQ, hT, e, hfix, hstable, heq⟩ :=
    cycle_permutation Q hQ f (fun i hi => (hfc i hi).1)
  let E : D.Exchange := {
    active := T
    e := e
    fixed := hfix
    stable := hstable
    a := a
    b := fun i => c (e.symm i)
    bounds := by
      intro i hi
      have hpre : e.symm i ∈ T := (hstable _).mpr (by simpa using hi)
      have he : f (e.symm i) = i := (heq _ hpre).symm.trans (e.apply_symm_apply i)
      have hc := (hfc _ (hTQ hpre)).2
      rw [he] at hc
      exact ⟨hc.1, hc.2.1⟩
    edge := by
      intro i hi
      have hc := (hfc i (hTQ hi)).2.2.2
      rw [← heq i hi] at hc
      simpa only [Equiv.symm_apply_apply] using hc
  }
  exact hD.no_exchange E hT

end BagRouting

end LinearListHadwiger

end OAI
