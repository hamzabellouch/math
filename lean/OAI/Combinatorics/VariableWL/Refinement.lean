import OAI.Combinatorics.VariableWL.Affine

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6

namespace VariableWL

private theorem map_univ_comp_equiv {A : Type uVariable1} {B : Type uVariable2} {C : Type uVariable3} [Fintype A] [Fintype B]
    (e : A ≃ B) (f : B → C) :
    Finset.univ.val.map f = Finset.univ.val.map (fun a => f (e a)) := by
  rw [← Multiset.map_univ_val_equiv e, Multiset.map_map]
  rfl

def tupleEquiv {G H : Graph} (e : G.graph ≃g H.graph) (k : ℕ) :
    Tuple G k ≃ Tuple H k where
  toFun v := e ∘ v
  invFun v := e.symm ∘ v
  left_inv v := by funext i; simp
  right_inv v := by funext i; simp

theorem color_iso {G H : Graph} (e : G.graph ≃g H.graph) (k : ℕ) :
    ∀ s (v : Tuple G k), color H k s (e ∘ v) = color G k s v := by
  classical
  intro s
  induction s with
  | zero =>
    intro v
    funext i j
    simp [color, e.injective.eq_iff, e.map_rel_iff]
  | succ s ih =>
    intro v
    apply Prod.ext (ih v)
    change Finset.univ.val.map (fun z => fun i =>
      color H k s (Function.update (e ∘ v) i z)) =
      Finset.univ.val.map (fun z => fun i => color G k s (Function.update v i z))
    rw [map_univ_comp_equiv e.toEquiv]
    apply Multiset.map_congr rfl
    intro z _
    funext i
    simpa only [Function.comp_update, RelIso.coe_fn_toEquiv] using ih (Function.update v i z)

theorem histogram_iso {G H : Graph} (e : G.graph ≃g H.graph) (k s : ℕ) :
    histogram H k s = histogram G k s := by
  unfold histogram
  rw [map_univ_comp_equiv (tupleEquiv e k)]
  apply Multiset.map_congr rfl
  intro v _
  exact color_iso e k s v

theorem equivalent_of_iso {G H : Graph} (e : G.graph ≃g H.graph) (k : ℕ) :
    Equivalent G H k := fun s => (histogram_iso e k s).symm

@[simp] theorem histogram_card (G : Graph) (k s : ℕ) :
    (histogram G k s).card = G.order ^ k := by
  simp [histogram, Tuple]

theorem equivalent_order {G H : Graph} {k : ℕ} (hk : k ≠ 0)
    (h : Equivalent G H k) : G.order = H.order := by
  have hc := congrArg Multiset.card (h 0)
  simp only [histogram_card] at hc
  exact Nat.pow_left_injective hk hc

theorem color_zero_eq_iff {G H : Graph} {k : ℕ} (v : Tuple G k) (w : Tuple H k) :
    color G k 0 v = color H k 0 w ↔
      (∀ i j, v i = v j ↔ w i = w j) ∧
      (∀ i j, G.graph.Adj (v i) (v j) ↔ H.graph.Adj (w i) (w j)) := by
  classical
  constructor
  · intro h
    have hi : ∀ i j, (v i = v j ↔ w i = w j) ∧
        (G.graph.Adj (v i) (v j) ↔ H.graph.Adj (w i) (w j)) := by
      intro i j
      have hc := congrFun (congrFun h i) j
      change (decide (v i = v j), decide (G.graph.Adj (v i) (v j))) =
        (decide (w i = w j), decide (H.graph.Adj (w i) (w j))) at hc
      simpa only [Prod.mk.injEq, decide_eq_decide] using hc
    exact ⟨fun i j => (hi i j).1, fun i j => (hi i j).2⟩
  · rintro ⟨he, ha⟩
    funext i j
    apply Prod.ext
    · exact decide_eq_decide.mpr (he i j)
    · exact decide_eq_decide.mpr (ha i j)

theorem exists_color_match {G H : Graph} {k s : ℕ}
    (h : histogram G k s = histogram H k s) (v : Tuple G k) :
    ∃ w : Tuple H k, color H k s w = color G k s v := by
  have hm : color G k s v ∈ histogram G k s :=
    Multiset.mem_map.mpr ⟨v, Finset.mem_univ_val v, rfl⟩
  rw [h] at hm
  rcases Multiset.mem_map.mp hm with ⟨w, _, hw⟩
  exact ⟨w, hw⟩

theorem iso_of_equivalent_large {G H : Graph} {k : ℕ} (hk : k ≠ 0)
    (hlarge : G.order ≤ k) (h : Equivalent G H k) : Nonempty (G.graph ≃g H.graph) := by
  classical
  have horder := equivalent_order hk h
  by_cases hz : G.order = 0
  · have : IsEmpty (Fin G.order) := ⟨fun v => by have := v.isLt; omega⟩
    have : IsEmpty (Fin H.order) := ⟨fun v => by have := v.isLt; omega⟩
    exact ⟨⟨Equiv.equivOfIsEmpty _ _, fun {i _} => isEmptyElim i⟩⟩
  have hn : 0 < G.order := Nat.pos_of_ne_zero hz
  let pick : Fin G.order → Fin k := fun x => ⟨x.val, lt_of_lt_of_le x.isLt hlarge⟩
  let v : Tuple G k := fun i => ⟨i.val % G.order, Nat.mod_lt _ hn⟩
  have hv : ∀ x, v (pick x) = x := by
    intro x
    apply Fin.ext
    exact Nat.mod_eq_of_lt x.isLt
  obtain ⟨w, hw⟩ := exists_color_match (h 0) v
  obtain ⟨heq, hadj⟩ := (color_zero_eq_iff v w).mp hw.symm
  let f : Fin G.order → Fin H.order := fun x => w (pick x)
  have hinj : Function.Injective f := by
    intro x y hxy
    have hxy' := (heq (pick x) (pick y)).mpr hxy
    simpa only [hv] using hxy'
  have hsurj : Function.Surjective f := by
    apply (Fintype.bijective_iff_injective_and_card f).mpr
      ⟨hinj, by simpa using horder⟩ |>.2
  refine ⟨⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, ?_⟩⟩
  intro x y
  change H.graph.Adj (w (pick x)) (w (pick y)) ↔ G.graph.Adj x y
  simpa only [hv] using (hadj (pick x) (pick y)).symm

theorem equivalent_large_iff_iso {G H : Graph} {k : ℕ} (hk : k ≠ 0)
    (hlarge : G.order ≤ k) :
    Equivalent G H k ↔ Nonempty (G.graph ≃g H.graph) := by
  constructor
  · exact iso_of_equivalent_large hk hlarge
  · rintro ⟨e⟩
    exact equivalent_of_iso e k

end VariableWL

namespace VariableWL

private def defaultColor (k : ℕ) : (s : ℕ) → Color k s
  | 0 => fun _ _ => (false, false)
  | s + 1 => (defaultColor k s, 0)

instance colorInhabited (k s : ℕ) : Inhabited (Color k s) := ⟨defaultColor k s⟩

abbrev TaggedTuple (G H : Graph) (k : ℕ) := Tuple G k ⊕ Tuple H k

noncomputable def tagColor (G H : Graph) (k s : ℕ) : TaggedTuple G H k → Color k s :=
  Sum.elim (color G k s) (color H k s)

def liftColor {k s t : ℕ} (f : Color k s → Color k t) : Color k (s+1) → Color k (t+1) :=
  fun c => (f c.1, c.2.map (fun a => f ∘ a))

theorem color_factor_succ {G : Graph} {k s t : ℕ} (f : Color k s → Color k t)
    (hf : ∀ v : Tuple G k, color G k t v = f (color G k s v)) (v : Tuple G k) :
    color G k (t+1) v = liftColor f (color G k (s+1) v) := by
  apply Prod.ext (hf v)
  change Finset.univ.val.map (fun z => fun i => color G k t (Function.update v i z)) =
    (Finset.univ.val.map (fun z => fun i => color G k s (Function.update v i z))).map
      (fun a => f ∘ a)
  rw [Multiset.map_map]
  apply Multiset.map_congr rfl
  intro z _
  funext i
  exact hf (Function.update v i z)

theorem tagColor_factor_succ {G H : Graph} {k s t : ℕ} (f : Color k s → Color k t)
    (hf : ∀ v, tagColor G H k t v = f (tagColor G H k s v)) (v : TaggedTuple G H k) :
    tagColor G H k (t+1) v = liftColor f (tagColor G H k (s+1) v) := by
  cases v with
  | inl v => exact color_factor_succ f (fun a => hf (.inl a)) v
  | inr v => exact color_factor_succ f (fun a => hf (.inr a)) v

theorem tagColor_eq_previous {G H : Graph} {k s : ℕ} {v w : TaggedTuple G H k}
    (h : tagColor G H k (s+1) v = tagColor G H k (s+1) w) :
    tagColor G H k s v = tagColor G H k s w := by
  have hp := congrArg Prod.fst h
  cases v <;> cases w <;> exact hp

def StableAt (G H : Graph) (k s : ℕ) : Prop :=
  (tagColor G H k (s+1)).FactorsThrough (tagColor G H k s)

private noncomputable def samePairs (G H : Graph) (k s : ℕ) :
    Finset (TaggedTuple G H k × TaggedTuple G H k) := by
  classical
  exact Finset.univ.filter (fun p => tagColor G H k s p.1 = tagColor G H k s p.2)

private theorem samePairs_next_subset (G H : Graph) (k s : ℕ) :
    samePairs G H k (s+1) ⊆ samePairs G H k s := by
  classical
  intro p hp
  simp only [samePairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  exact tagColor_eq_previous hp

private theorem exists_nat_plateau (a : ℕ → ℕ) (hmono : ∀ n, a (n+1) ≤ a n) :
    ∃ n ≤ a 0, a (n+1) = a n := by
  by_contra! h
  have hstrict : ∀ n ≤ a 0, a (n+1) < a n := by
    intro n hn
    exact lt_of_le_of_ne (hmono n) (h n hn)
  have hbound : ∀ n ≤ a 0 + 1, a n + n ≤ a 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro hn
      have hprev := ih (by omega)
      have hstep := hstrict n (by omega)
      omega
  have := hbound (a 0 + 1) le_rfl
  omega

theorem exists_stable_round (G H : Graph) (k : ℕ) :
    ∃ s ≤ (G.order ^ k + H.order ^ k) ^ 2, StableAt G H k s := by
  classical
  obtain ⟨s, hs, heq⟩ := exists_nat_plateau
    (fun n => (samePairs G H k n).card)
    (fun n => Finset.card_le_card (samePairs_next_subset G H k n))
  have hsets : samePairs G H k (s+1) = samePairs G H k s :=
    Finset.eq_of_subset_of_card_le (samePairs_next_subset G H k s) heq.ge
  refine ⟨s, ?_, ?_⟩
  · refine hs.trans ?_
    calc
      (samePairs G H k 0).card ≤ Fintype.card (TaggedTuple G H k × TaggedTuple G H k) :=
        Finset.card_le_univ _
      _ = (G.order ^ k + H.order ^ k) ^ 2 := by
        simp [TaggedTuple, Tuple, pow_two]
  · intro v w hvw
    have hm : (v, w) ∈ samePairs G H k s := by
      simp [samePairs, hvw]
    rw [← hsets] at hm
    simpa only [samePairs, Finset.mem_filter, Finset.mem_univ, true_and] using hm

theorem stable_later_factor {G H : Graph} {k s : ℕ} (hs : StableAt G H k s) :
    ∀ t, ∃ f : Color k s → Color k (s+t),
      ∀ v, tagColor G H k (s+t) v = f (tagColor G H k s v) := by
  obtain ⟨f₀, hf₀⟩ := (Function.factorsThrough_iff (tagColor G H k (s+1))).mp hs
  have hbase : ∀ v, tagColor G H k (s+1) v = f₀ (tagColor G H k s v) :=
    fun v => congrFun hf₀ v
  intro t
  induction t with
  | zero => exact ⟨id, fun _ => rfl⟩
  | succ t ih =>
    obtain ⟨f, hf⟩ := ih
    refine ⟨liftColor f ∘ f₀, ?_⟩
    intro v
    calc
      tagColor G H k (s+(t+1)) v = liftColor f (tagColor G H k (s+1) v) :=
        tagColor_factor_succ f hf v
      _ = (liftColor f ∘ f₀) (tagColor G H k s v) := by rw [hbase]; rfl

@[simp] theorem histogram_fst (G : Graph) (k s : ℕ) :
    (histogram G k (s+1)).map Prod.fst = histogram G k s := by
  exact (Multiset.map_map Prod.fst (color G k (s+1)) Finset.univ.val)

theorem histogram_eq_previous {G H : Graph} {k s : ℕ}
    (h : histogram G k (s+1) = histogram H k (s+1)) :
    histogram G k s = histogram H k s := by
  simpa only [histogram_fst] using congrArg (Multiset.map Prod.fst) h

theorem histogram_eq_of_le {G H : Graph} {k s t : ℕ} (hle : s ≤ t)
    (h : histogram G k t = histogram H k t) : histogram G k s = histogram H k s := by
  induction t generalizing s with
  | zero => have : s = 0 := Nat.eq_zero_of_le_zero hle; subst s; exact h
  | succ t ih =>
    by_cases he : s = t + 1
    · subst s; exact h
    · exact ih (by omega) (histogram_eq_previous h)

theorem histogram_eq_later {G H : Graph} {k s : ℕ} (hs : StableAt G H k s)
    (h : histogram G k s = histogram H k s) (t : ℕ) :
    histogram G k (s+t) = histogram H k (s+t) := by
  obtain ⟨f, hf⟩ := stable_later_factor hs t
  have hG : histogram G k (s+t) = (histogram G k s).map f := by
    simp only [histogram, Multiset.map_map]
    apply Multiset.map_congr rfl
    intro v _
    exact hf (.inl v)
  have hH : histogram H k (s+t) = (histogram H k s).map f := by
    simp only [histogram, Multiset.map_map]
    apply Multiset.map_congr rfl
    intro v _
    exact hf (.inr v)
  rw [hG, hH, h]

theorem equivalent_iff_bounded_round (G H : Graph) (k : ℕ) :
    Equivalent G H k ↔
      histogram G k ((G.order ^ k + H.order ^ k) ^ 2) =
      histogram H k ((G.order ^ k + H.order ^ k) ^ 2) := by
  constructor
  · intro h; exact h _
  · intro hn
    obtain ⟨s, hs, hstable⟩ := exists_stable_round G H k
    have heq := histogram_eq_of_le hs hn
    intro t
    by_cases ht : t ≤ s
    · exact histogram_eq_of_le ht heq
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt (Nat.lt_of_not_ge ht))
      exact histogram_eq_later hstable heq d

end VariableWL

namespace VariableWL

theorem exists_equiv_of_map_univ_eq {α : Type uVariable4} {β : Type uVariable5} {γ : Type uVariable6} [Fintype α] [Fintype β]
    (f : α → γ) (g : β → γ)
    (h : Finset.univ.val.map f = Finset.univ.val.map g) :
    ∃ e : α ≃ β, ∀ a, f a = g (e a) := by
  classical
  have hc (c : γ) : Fintype.card {a // f a = c} = Fintype.card {b // g b = c} := by
    have hh := congrArg (Multiset.count c) h
    simpa only [Multiset.count_map, ← Finset.filter_val, ← Finset.card_def,
      Fintype.card_subtype, eq_comm (a := c)] using hh
  let e (c : γ) : {a // f a = c} ≃ {b // g b = c} := Fintype.equivOfCardEq (hc c)
  exact ⟨Equiv.ofFiberEquiv e, fun a => (Equiv.ofFiberEquiv_map e a).symm⟩

noncomputable def permColor {k : ℕ} (e : Equiv.Perm (Fin k)) :
    (s : ℕ) → Color k s → Color k s
  | 0, c => fun i j => c (e i) (e j)
  | s+1, c => (permColor e s c.1,
      c.2.map (fun p i => permColor e s (p (e i))))

theorem color_reindex (G : Graph) (k s : ℕ) (e : Equiv.Perm (Fin k)) (v : Tuple G k) :
    color G k s (v ∘ e) = permColor e s (color G k s v) := by
  classical
  induction s generalizing v with
  | zero => rfl
  | succ s ih =>
    change (color G k s (v ∘ e), _) = (permColor e s (color G k s v), _)
    apply Prod.ext (ih v)
    change (Finset.univ.val.map (fun z i => color G k s (Function.update (v ∘ e) i z))) =
      (Finset.univ.val.map (fun z i => color G k s (Function.update v i z))).map
        (fun p i => permColor e s (p (e i)))
    rw [Multiset.map_map]
    apply Multiset.map_congr rfl
    intro z _
    funext i
    rw [← Function.update_comp_eq_of_injective v e.injective]
    exact ih _

def StableEq {G H : Graph} {k : ℕ} (v : Tuple G k) (w : Tuple H k) : Prop :=
  ∀ s, color G k s v = color H k s w

theorem StableEq.reindex {G H : Graph} {k : ℕ} {v : Tuple G k} {w : Tuple H k}
    (h : StableEq v w) (e : Equiv.Perm (Fin k)) : StableEq (v ∘ e) (w ∘ e) := by
  intro s
  rw [color_reindex, color_reindex, h s]

theorem color_eq_previous {G H : Graph} {k s : ℕ} {v : Tuple G k} {w : Tuple H k}
    (h : color G k (s+1) v = color H k (s+1) w) :
    color G k s v = color H k s w := congrArg Prod.fst h

theorem color_eq_of_le {G H : Graph} {k s t : ℕ} {v : Tuple G k} {w : Tuple H k}
    (hle : s ≤ t) (h : color G k t v = color H k t w) :
    color G k s v = color H k s w := by
  induction t generalizing s with
  | zero => have : s = 0 := Nat.eq_zero_of_le_zero hle; subst s; exact h
  | succ t ih =>
    by_cases he : s = t+1
    · subst s; exact h
    · exact ih (by omega) (color_eq_previous h)

theorem stableEq_of_color_eq {G H : Graph} {k s : ℕ} (hs : StableAt G H k s)
    {v : Tuple G k} {w : Tuple H k} (h : color G k s v = color H k s w) :
    StableEq v w := by
  intro t
  by_cases ht : t ≤ s
  · exact color_eq_of_le ht h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt (Nat.lt_of_not_ge ht))
    obtain ⟨f, hf⟩ := stable_later_factor hs d
    exact (hf (.inl v)).trans ((congrArg f h).trans (hf (.inr w)).symm)

theorem StableEq.exists_bijection {G H : Graph} {k : ℕ}
    {v : Tuple G k} {w : Tuple H k} (h : StableEq v w) :
    ∃ e : Fin G.order ≃ Fin H.order, ∀ z i,
      StableEq (Function.update v i z) (Function.update w i (e z)) := by
  classical
  obtain ⟨s, _, hs⟩ := exists_stable_round G H k
  have hprof : Finset.univ.val.map (fun z i => color G k s (Function.update v i z)) =
      Finset.univ.val.map (fun z i => color H k s (Function.update w i z)) :=
    congrArg Prod.snd (h (s+1))
  obtain ⟨e, he⟩ := exists_equiv_of_map_univ_eq _ _ hprof
  exact ⟨e, fun z i => stableEq_of_color_eq hs (congrFun (he z) i)⟩

end VariableWL

universe uGame1 uGame2 uGame3 uGame4 uGame5 uGame6 uGame7

namespace VariableWL.Game

abbrev Position (G H : Graph) (q : ℕ) := Fin q → Option (Fin G.order × Fin H.order)

def PartialIso {G H : Graph} {q : ℕ} (p : Position G H q) : Prop :=
  ∀ i j a b, p i = some a → p j = some b →
    (a.1 = b.1 ↔ a.2 = b.2) ∧ (G.graph.Adj a.1 b.1 ↔ H.graph.Adj a.2 b.2)

def Subposition {G H : Graph} {q : ℕ} (p' p : Position G H q) : Prop :=
  ∀ i a, p' i = some a → p i = some a

def WinningFamily {G H : Graph} {q : ℕ} (S : Set (Position G H q)) : Prop :=
  (∀ p ∈ S, PartialIso p) ∧
  (∀ p ∈ S, ∀ p', Subposition p' p → p' ∈ S) ∧
  (∀ p ∈ S, ∀ i, p i = none → ∃ e : Fin G.order ≃ Fin H.order,
    ∀ v, Function.update p i (some (v, e v)) ∈ S)

def Winning {G H : Graph} {q : ℕ} (p : Position G H q) : Prop :=
  ∃ S, p ∈ S ∧ WinningFamily S

theorem Winning.partialIso {G H : Graph} {q : ℕ} {p : Position G H q}
    (h : Winning p) : PartialIso p := by
  obtain ⟨S, hp, hS⟩ := h
  exact hS.1 p hp

theorem Winning.discard {G H : Graph} {q : ℕ} {p p' : Position G H q}
    (h : Winning p) (hp' : Subposition p' p) : Winning p' := by
  obtain ⟨S, hp, hS⟩ := h
  exact ⟨S, hS.2.1 p hp p' hp', hS⟩

theorem Winning.move {G H : Graph} {q : ℕ} {p : Position G H q}
    (h : Winning p) (i : Fin q) (hi : p i = none) :
    ∃ e : Fin G.order ≃ Fin H.order, ∀ v,
      Winning (Function.update p i (some (v, e v))) := by
  obtain ⟨S, hp, hS⟩ := h
  obtain ⟨e, he⟩ := hS.2.2 p hp i hi
  exact ⟨e, fun v => ⟨S, he v, hS⟩⟩

theorem clear_subposition {G H : Graph} {q : ℕ} (p : Position G H q) (j : Fin q) :
    Subposition (Function.update p j none) p := by
  intro i a hi
  by_cases h : i = j
  · subst i; simp at hi
  · simpa [Function.update_of_ne h] using hi

def Realizes {G H : Graph} {q k : ℕ} (p : Position G H q)
    (σ : Fin k → Fin q) (v : Tuple G k) (w : Tuple H k) : Prop :=
  ∀ i, p (σ i) = some (v i, w i)

theorem exists_fresh {k : ℕ} (σ : Fin k → Fin (k+1)) :
    ∃ j, ∀ i, σ i ≠ j := by
  by_contra! h
  have hsurj : Function.Surjective σ := fun j => by simpa using h j
  have hc := Fintype.card_le_of_surjective σ hsurj
  simp at hc

theorem update_injective_of_fresh {α : Type uGame1} {β : Type uGame2} [DecidableEq α]
    {f : α → β} (hf : Function.Injective f) (i : α) (b : β)
    (hb : ∀ a, f a ≠ b) : Function.Injective (Function.update f i b) := by
  intro x y hxy
  by_cases hx : x = i <;> by_cases hy : y = i
  · exact hx.trans hy.symm
  · subst x
    simp only [Function.update_self, Function.update_of_ne hy] at hxy
    exact (hb y hxy.symm).elim
  · subst y
    simp only [Function.update_self, Function.update_of_ne hx] at hxy
    exact (hb x hxy).elim
  · simp only [Function.update_of_ne hx, Function.update_of_ne hy] at hxy
    exact hf hxy

theorem Winning.color_eq {G H : Graph} {k : ℕ} {p : Position G H (k+1)}
    (hp : Winning p) (σ : Fin k → Fin (k+1)) (hσ : Function.Injective σ)
    (v : Tuple G k) (w : Tuple H k) (hr : Realizes p σ v w) (s : ℕ) :
    color G k s v = color H k s w := by
  classical
  induction s generalizing p σ v w with
  | zero =>
    apply (color_zero_eq_iff v w).mpr
    have h := hp.partialIso
    exact ⟨fun i j => (h (σ i) (σ j) _ _ (hr i) (hr j)).1,
      fun i j => (h (σ i) (σ j) _ _ (hr i) (hr j)).2⟩
  | succ s ih =>
    apply Prod.ext (ih hp σ hσ v w hr)
    obtain ⟨j, hj⟩ := exists_fresh σ
    let p₀ := Function.update p j none
    have hp₀ : Winning p₀ := hp.discard (clear_subposition p j)
    obtain ⟨e, he⟩ := hp₀.move j (by simp [p₀])
    change Finset.univ.val.map (fun z i => color G k s (Function.update v i z)) =
      Finset.univ.val.map (fun z i => color H k s (Function.update w i z))
    rw [map_univ_comp_equiv e]
    apply Multiset.map_congr rfl
    intro z _
    funext i
    apply ih (he z) (Function.update σ i j) (update_injective_of_fresh hσ i j hj)
    intro a
    by_cases ha : a = i
    · subst a; simp
    · simp only [Function.update_of_ne ha, Function.update_of_ne (hj a)]
      simpa [p₀, Function.update_of_ne (hj a)] using hr a

end VariableWL.Game

namespace VariableWL.Game

theorem Subposition.refl {G H : Graph} {q : ℕ} (p : Position G H q) :
    Subposition p p := fun _ _ => id

theorem Subposition.trans {G H : Graph} {q : ℕ} {p₁ p₂ p₃ : Position G H q}
    (h₁ : Subposition p₁ p₂) (h₂ : Subposition p₂ p₃) : Subposition p₁ p₃ :=
  fun i a ha => h₂ i a (h₁ i a ha)

theorem place_extends {G H : Graph} {q : ℕ} (p : Position G H q) (i : Fin q)
    (hi : p i = none) (a : Fin G.order × Fin H.order) :
    Subposition p (Function.update p i (some a)) := by
  intro j b hj
  by_cases hji : j = i
  · subst j; rw [hi] at hj; contradiction
  · simpa [Function.update_of_ne hji] using hj

def triangularEquiv {A : Type uGame3} {B : Type uGame4} {C : Type uGame5} {D : Type uGame6} (e : A ≃ B) (E : A → C ≃ D) :
    (A × C) ≃ (B × D) where
  toFun a := (e a.1, E a.1 a.2)
  invFun b := (e.symm b.1, (E (e.symm b.1)).symm b.2)
  left_inv a := by simp
  right_inv b := by simp

theorem Winning.fill {G H : Graph} {q : ℕ} {p : Position G H q} (hp : Winning p)
    (n : ℕ) (σ : Fin n → Fin q) (hσ : Function.Injective σ)
    (hfree : ∀ i, p (σ i) = none) :
    ∃ E : Tuple G n ≃ Tuple H n, ∀ v, ∃ p' : Position G H q,
      Winning p' ∧ Subposition p p' ∧ Realizes p' σ v (E v) := by
  classical
  induction n generalizing p with
  | zero =>
    refine ⟨Equiv.piCongrRight (fun i : Fin 0 => Fin.elim0 i), ?_⟩
    intro v
    exact ⟨p, hp, Subposition.refl p, fun i => Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨e, he⟩ := hp.move (σ 0) (hfree 0)
    have ht (z : Fin G.order) :
        ∃ E : Tuple G n ≃ Tuple H n, ∀ v, ∃ p' : Position G H q,
          Winning p' ∧ Subposition (Function.update p (σ 0) (some (z, e z))) p' ∧
          Realizes p' (σ ∘ Fin.succ) v (E v) := by
      apply ih (he z) (σ ∘ Fin.succ) (hσ.comp (Fin.succ_injective n))
      intro i
      rw [Function.update_of_ne]
      · exact hfree i.succ
      · intro h
        exact Fin.succ_ne_zero i (hσ h)
    choose E hE using ht
    let F : Tuple G (n+1) ≃ Tuple H (n+1) :=
      (Fin.consEquiv (fun _ : Fin (n+1) => Fin G.order)).symm |>.trans
        ((triangularEquiv e E).trans (Fin.consEquiv (fun _ : Fin (n+1) => Fin H.order)))
    refine ⟨F, ?_⟩
    intro v
    obtain ⟨p', hp', hsub, hreal⟩ := hE (v 0) (Fin.tail v)
    refine ⟨p', hp', (place_extends p (σ 0) (hfree 0) _).trans hsub, ?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change p' (σ 0) = some (v 0, e (v 0))
      exact hsub (σ 0) _ (by simp)
    · exact hreal j

theorem equivalent_of_winning {G H : Graph} {k : ℕ}
    (h : Winning (fun _ : Fin (k+1) => (none : Option (Fin G.order × Fin H.order)))) :
    Equivalent G H k := by
  obtain ⟨E, hE⟩ := h.fill k Fin.castSucc (Fin.castSucc_injective k) (fun _ => rfl)
  intro s
  unfold histogram
  rw [map_univ_comp_equiv E]
  apply Multiset.map_congr rfl
  intro v _
  obtain ⟨p, hp, _, hr⟩ := hE v
  exact hp.color_eq Fin.castSucc (Fin.castSucc_injective k) v (E v) hr s

end VariableWL.Game

namespace VariableWL.Game

theorem reindex_embeddings {α : Type uGame7} {k : ℕ} (f g : Fin k → α)
    (hg : Function.Injective g) (hr : ∀ i, ∃ j, f j = g i) :
    ∃ e : Equiv.Perm (Fin k), g = f ∘ e := by
  classical
  choose a ha using hr
  have hinj : Function.Injective a := by
    intro i j hij
    apply hg
    rw [← ha i, ← ha j, hij]
  let e := Equiv.ofBijective a
    ((Fintype.bijective_iff_injective_and_card a).mpr ⟨hinj, rfl⟩)
  exact ⟨e, funext fun i => (ha i).symm⟩

def FullStable {G H : Graph} {k : ℕ}
    (v : Fin (k+1) → Fin G.order) (w : Fin (k+1) → Fin H.order) : Prop :=
  ∀ σ : Fin k ↪ Fin (k+1), StableEq (v ∘ σ) (w ∘ σ)

theorem fullStable_update {G H : Graph} {k : ℕ}
    (v : Fin (k+1) → Fin G.order) (w : Fin (k+1) → Fin H.order)
    (j : Fin (k+1)) (z : Fin G.order) (t : Fin H.order)
    (hbase : StableEq (v ∘ j.succAbove) (w ∘ j.succAbove))
    (hrep : ∀ a, StableEq (Function.update (v ∘ j.succAbove) a z)
      (Function.update (w ∘ j.succAbove) a t)) :
    FullStable (Function.update v j z) (Function.update w j t) := by
  classical
  intro τ
  obtain ⟨m, hm⟩ := exists_fresh τ
  by_cases hmj : m = j
  · subst m
    obtain ⟨e, he⟩ := reindex_embeddings j.succAbove τ τ.injective
      (fun b => Fin.exists_succAbove_eq (hm b))
    have hG : Function.update v j z ∘ τ = (v ∘ j.succAbove) ∘ e := by
      funext b
      simp only [Function.comp_apply, Function.update_of_ne (hm b)]
      exact congrArg v (congrFun he b)
    have hH : Function.update w j t ∘ τ = (w ∘ j.succAbove) ∘ e := by
      funext b
      simp only [Function.comp_apply, Function.update_of_ne (hm b)]
      exact congrArg w (congrFun he b)
    rw [hG, hH]
    exact hbase.reindex e
  · obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hmj
    let σ' := Function.update j.succAbove a j
    have hr : ∀ b, ∃ c, σ' c = τ b := by
      intro b
      by_cases hb : τ b = j
      · exact ⟨a, by simp [σ', hb]⟩
      · obtain ⟨c, hc⟩ := Fin.exists_succAbove_eq hb
        have hca : c ≠ a := by
          intro hca
          exact hm b (hc.symm.trans (hca ▸ ha))
        exact ⟨c, by simpa [σ', Function.update_of_ne hca] using hc⟩
    obtain ⟨e, he⟩ := reindex_embeddings σ' τ τ.injective hr
    have hcomp {A : Type} (u : Fin (k+1) → A) (x : A) :
        Function.update u j x ∘ σ' = Function.update (u ∘ j.succAbove) a x := by
      funext b
      by_cases hb : b = a
      · subst b; simp [σ']
      · simp [σ', Function.update_of_ne hb, Function.comp_apply, Fin.succAbove_ne]
    rw [he, ← Function.comp_assoc, hcomp, ← Function.comp_assoc, hcomp]
    exact (hrep a).reindex e

theorem FullStable.atomic {G H : Graph} {k : ℕ} (hk : 2 ≤ k)
    {v : Fin (k+1) → Fin G.order} {w : Fin (k+1) → Fin H.order}
    (h : FullStable v w) (i j : Fin (k+1)) :
    (v i = v j ↔ w i = w j) ∧ (G.graph.Adj (v i) (v j) ↔ H.graph.Adj (w i) (w j)) := by
  obtain ⟨m, hmi, hmj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega)
  obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hmi.symm
  obtain ⟨b, hb⟩ := Fin.exists_succAbove_eq hmj.symm
  have hc := (color_zero_eq_iff _ _).mp (h m.succAboveEmb 0)
  have h₁ := hc.1 a b
  have h₂ := hc.2 a b
  simp only [Function.comp_apply, Fin.coe_succAboveEmb, ha, hb] at h₁ h₂
  exact ⟨h₁, h₂⟩

end VariableWL.Game

namespace VariableWL.Game

def Fits {G H : Graph} {k : ℕ} (p : Position G H (k+1))
    (v : Fin (k+1) → Fin G.order) (w : Fin (k+1) → Fin H.order) : Prop :=
  ∀ i a, p i = some a → v i = a.1 ∧ w i = a.2

def GhostFamily (G H : Graph) (k : ℕ) : Set (Position G H (k+1)) :=
  {p | ∃ v w, FullStable v w ∧ Fits p v w}

theorem ghostFamily_winning (G H : Graph) (k : ℕ) (hk : 2 ≤ k) :
    WinningFamily (GhostFamily G H k) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · rintro p ⟨v, w, hs, hf⟩ i j a b hia hjb
    obtain ⟨hvi, hwi⟩ := hf i a hia
    obtain ⟨hvj, hwj⟩ := hf j b hjb
    simpa only [hvi, hwi, hvj, hwj] using hs.atomic hk i j
  · rintro p ⟨v, w, hs, hf⟩ p' hsub
    exact ⟨v, w, hs, fun i a ha => hf i a (hsub i a ha)⟩
  · rintro p ⟨v, w, hs, hf⟩ j _
    have hbase := hs j.succAboveEmb
    obtain ⟨e, he⟩ := hbase.exists_bijection
    refine ⟨e, fun z => ?_⟩
    refine ⟨Function.update v j z, Function.update w j (e z),
      fullStable_update v w j z (e z) hbase (he z), ?_⟩
    intro i a ha
    by_cases hij : i = j
    · subst i
      simp only [Function.update_self, Option.some.injEq] at ha
      subst a
      simp
    · simp only [Function.update_of_ne hij] at ha ⊢
      exact hf i a ha

theorem exists_fullStable {G H : Graph} {k : ℕ} (hG : 0 < G.order)
    (h : Equivalent G H k) :
    ∃ v : Fin (k+1) → Fin G.order, ∃ w : Fin (k+1) → Fin H.order, FullStable v w := by
  classical
  let z : Fin G.order := ⟨0, hG⟩
  let v : Tuple G k := fun _ => z
  obtain ⟨s, _, hs⟩ := exists_stable_round G H k
  obtain ⟨w, hw⟩ := exists_color_match (h s) v
  have hb : StableEq v w := stableEq_of_color_eq hs hw.symm
  obtain ⟨e, he⟩ := hb.exists_bijection
  let j := Fin.last k
  let V : Fin (k+1) → Fin G.order := Fin.insertNth j z v
  let W : Fin (k+1) → Fin H.order := Fin.insertNth j (e z) w
  have hv : V ∘ j.succAbove = v := Fin.insertNth_comp_succAbove j z v
  have hw' : W ∘ j.succAbove = w := Fin.insertNth_comp_succAbove j (e z) w
  refine ⟨Function.update V j z, Function.update W j (e z), ?_⟩
  apply fullStable_update V W j z (e z)
  · simpa only [hv, hw'] using hb
  · simpa only [hv, hw'] using he z

theorem winning_of_equivalent {G H : Graph} {k : ℕ} (hk : 2 ≤ k)
    (hG : 0 < G.order) (h : Equivalent G H k) :
    Winning (fun _ : Fin (k+1) => (none : Option (Fin G.order × Fin H.order))) := by
  obtain ⟨v, w, hvw⟩ := exists_fullStable hG h
  refine ⟨GhostFamily G H k, ⟨v, w, hvw, ?_⟩, ghostFamily_winning G H k hk⟩
  intro i a ha
  contradiction

theorem equivalent_iff_winning {G H : Graph} {k : ℕ} (hk : 2 ≤ k) (hG : 0 < G.order) :
    Equivalent G H k ↔
      Winning (fun _ : Fin (k+1) => (none : Option (Fin G.order × Fin H.order))) :=
  ⟨winning_of_equivalent hk hG, equivalent_of_winning⟩

end VariableWL.Game

namespace VariableWL.Game

inductive Action (G H : Graph) (q : ℕ) where
  | discard : Position G H q → Action G H q
  | place : Fin q → (Fin G.order ≃ Fin H.order) → Fin G.order → Action G H q

def historyPosition {G H : Graph} {q : ℕ} : List (Action G H q) → Position G H q
  | [] => fun _ => none
  | .discard p :: _ => p
  | .place i e v :: h => Function.update (historyPosition h) i (some (v, e v))

abbrev Strategy (G H : Graph) (q : ℕ) :=
  List (Action G H q) → Fin q → Option (Fin G.order ≃ Fin H.order)

inductive Reached {G H : Graph} {q : ℕ} (S : Strategy G H q) :
    List (Action G H q) → Prop where
  | nil : Reached S []
  | discard {h p} : Reached S h → Subposition p (historyPosition h) →
      Reached S (.discard p :: h)
  | place {h i e v} : Reached S h → historyPosition h i = none → S h i = some e →
      Reached S (.place i e v :: h)

def StrategyWins {G H : Graph} {q : ℕ} (S : Strategy G H q) : Prop :=
  ∀ h, Reached S h → PartialIso (historyPosition h) ∧
    ∀ i, historyPosition h i = none → ∃ e, S h i = some e

theorem winning_of_strategy {G H : Graph} {q : ℕ} (S : Strategy G H q)
    (hS : StrategyWins S) : Winning (fun _ : Fin q => (none : Option (Fin G.order × Fin H.order))) := by
  let A : Set (Position G H q) := {p | ∃ h, Reached S h ∧ historyPosition h = p}
  refine ⟨A, ⟨[], .nil, rfl⟩, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · rintro p ⟨h, hh, rfl⟩
    exact (hS h hh).1
  · rintro p ⟨h, hh, rfl⟩ p' hp'
    exact ⟨.discard p' :: h, .discard hh hp', rfl⟩
  · rintro p ⟨h, hh, rfl⟩ i hi
    obtain ⟨e, he⟩ := (hS h hh).2 i hi
    exact ⟨e, fun v => ⟨.place i e v :: h, .place hh hi he, rfl⟩⟩

noncomputable def invariantStrategy (G H : Graph) (q : ℕ) : Strategy G H q := by
  classical
  exact fun h i => if hw : Winning (historyPosition h) ∧ historyPosition h i = none
    then some (Classical.choose (hw.1.move i hw.2)) else none

theorem invariantStrategy_reached {G H : Graph} {q : ℕ}
    (hp : Winning (fun _ : Fin q => (none : Option (Fin G.order × Fin H.order))))
    {h : List (Action G H q)} (hh : Reached (invariantStrategy G H q) h) :
    Winning (historyPosition h) := by
  classical
  induction hh with
  | nil => exact hp
  | discard hh hsub ih => exact ih.discard hsub
  | @place h i e v hh hi he ih =>
    have hw : Winning (historyPosition h) ∧ historyPosition h i = none := ⟨ih, hi⟩
    have heq : Classical.choose (hw.1.move i hw.2) = e := by
      simpa only [invariantStrategy, dite_eq_left hw, Option.some.injEq] using he
    have hm := Classical.choose_spec (hw.1.move i hw.2) v
    rw [heq] at hm
    exact hm

theorem strategy_of_winning {G H : Graph} {q : ℕ}
    (hp : Winning (fun _ : Fin q => (none : Option (Fin G.order × Fin H.order)))) :
    ∃ S : Strategy G H q, StrategyWins S := by
  classical
  refine ⟨invariantStrategy G H q, ?_⟩
  intro h hh
  have hw := invariantStrategy_reached hp hh
  refine ⟨hw.partialIso, ?_⟩
  intro i hi
  refine ⟨Classical.choose (hw.move i hi), ?_⟩
  simp only [invariantStrategy, dite_eq_left (show Winning (historyPosition h) ∧
    historyPosition h i = none from ⟨hw, hi⟩)]

theorem empty_winning_iff_strategy {G H : Graph} {q : ℕ} :
    Winning (fun _ : Fin q => (none : Option (Fin G.order × Fin H.order))) ↔
      ∃ S : Strategy G H q, StrategyWins S :=
  ⟨strategy_of_winning, fun ⟨S, hS⟩ => winning_of_strategy S hS⟩

theorem wl_iff_announced_strategy {G H : Graph} {k : ℕ} (hk : 2 ≤ k)
    (hG : 0 < G.order) : Equivalent G H k ↔
      ∃ S : Strategy G H (k+1), StrategyWins S :=
  (equivalent_iff_winning hk hG).trans empty_winning_iff_strategy

end VariableWL.Game

end OAI
