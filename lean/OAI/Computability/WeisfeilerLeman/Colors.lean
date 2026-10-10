import OAI.Computability.WeisfeilerLeman.Model

namespace OAI

universe uα uβ uC uγ

namespace WLTime

theorem equiv_of_multiset_match {α : Type uα} {β : Type uβ} {C : Type uC} [Fintype α] [Fintype β]
    (f : α → C) (g : β → C)
    (h : Finset.univ.val.map f = Finset.univ.val.map g) :
    ∃ e : α ≃ β, ∀ a, f a = g (e a) := by
  classical
  have hfiber (c : C) : Fintype.card {a // f a = c} = Fintype.card {b // g b = c} := by
    have hc := congrArg (Multiset.count c) h
    simpa only [Multiset.count_map, Fintype.card_subtype, Finset.card_def,
      Finset.filter_val, eq_comm] using hc
  let e (c : C) := Fintype.equivOfCardEq (hfiber c)
  exact ⟨Equiv.ofFiberEquiv e, fun a => (Equiv.ofFiberEquiv_map e a).symm⟩

theorem multiset_match_of_equiv {α : Type uα} {β : Type uβ} {C : Type uC} [Fintype α] [Fintype β]
    (f : α → C) (g : β → C) (e : α ≃ β) (h : ∀ a, f a = g (e a)) :
    Finset.univ.val.map f = Finset.univ.val.map g := by
  have he : Finset.univ.val.map e = (Finset.univ : Finset β).val := by
    exact (Finset.map_val e.toEmbedding Finset.univ).symm.trans
      (congrArg Finset.val (Finset.univ_map_equiv_to_embedding e))
  rw [← he, Multiset.map_map]
  exact Multiset.map_congr rfl (fun a _ => h a)

theorem finite_decreasing_choice {α : Type uα} [Fintype α] (R : ℕ → α → Prop)
    (mono : ∀ s t, s ≤ t → ∀ a, R t a → R s a)
    (exists_at : ∀ t, ∃ a, R t a) : ∃ a, ∀ t, R t a := by
  classical
  by_contra! h
  choose t ht using h
  obtain ⟨a, ha⟩ := exists_at (Finset.univ.sup t)
  exact ht a (mono _ _ (Finset.le_sup (Finset.mem_univ a)) a ha)

theorem tupleColor_eq_of_le {n k s t : ℕ} {c : Convention} {G H : Graph n}
    {v w : Fin k → Fin n} (hst : s ≤ t)
    (heq : tupleColor c k G t v = tupleColor c k H t w) :
    tupleColor c k G s v = tupleColor c k H s w := by
  induction hst with
  | refl => exact heq
  | @step t h ih =>
    apply ih
    cases c <;> exact congrArg Prod.fst heq

def Stable {n : ℕ} (c : Convention) (k : ℕ) (G H : Graph n)
    (v w : Fin k → Fin n) : Prop := ∀ t, tupleColor c k G t v = tupleColor c k H t w

theorem equivalent_stable_matching {n k : ℕ} {c : Convention} {G H : Graph n}
    (heq : Equivalent c k G H) :
    ∃ e : (Fin k → Fin n) ≃ (Fin k → Fin n), ∀ v, Stable c k G H v (e v) := by
  classical
  have h := finite_decreasing_choice
    (fun t (e : (Fin k → Fin n) ≃ (Fin k → Fin n)) =>
      ∀ v, tupleColor c k G t v = tupleColor c k H t (e v))
    (fun s t hst e he v => tupleColor_eq_of_le hst (he v))
    (fun t => equiv_of_multiset_match _ _ (heq t))
  obtain ⟨e, he⟩ := h
  exact ⟨e, fun v t => he t v⟩

theorem stable_joint_extension {n k : ℕ} {G H : Graph n} {v w : Fin k → Fin n}
    (h : Stable .joint k G H v w) :
    ∃ e : Fin n ≃ Fin n, ∀ z i,
      Stable .joint k G H (Function.update v i z) (Function.update w i (e z)) := by
  classical
  have hmatch (t : ℕ) : ∃ e : Fin n ≃ Fin n, ∀ z i,
      tupleColor .joint k G t (Function.update v i z) =
        tupleColor .joint k H t (Function.update w i (e z)) := by
    have ht := congrArg Prod.snd (h (t + 1))
    dsimp only [tupleColor] at ht
    obtain ⟨e, he⟩ := equiv_of_multiset_match _ _ ht
    exact ⟨e, fun z i => congrFun (he z) i⟩
  obtain ⟨e, he⟩ := finite_decreasing_choice _
    (fun s t hst e he z i => tupleColor_eq_of_le hst (he z i)) hmatch
  exact ⟨e, fun z i t => he t z i⟩

theorem stable_separate_extension {n k : ℕ} {G H : Graph n} {v w : Fin k → Fin n}
    (h : Stable .separate k G H v w) (i : Fin k) :
    ∃ e : Fin n ≃ Fin n, ∀ z,
      Stable .separate k G H (Function.update v i z) (Function.update w i (e z)) := by
  classical
  have hmatch (t : ℕ) : ∃ e : Fin n ≃ Fin n, ∀ z,
      tupleColor .separate k G t (Function.update v i z) =
        tupleColor .separate k H t (Function.update w i (e z)) := by
    have ht := congrFun (congrArg Prod.snd (h (t + 1))) i
    dsimp only [tupleColor] at ht
    exact equiv_of_multiset_match _ _ ht
  obtain ⟨e, he⟩ := finite_decreasing_choice _
    (fun s t hst e he z => tupleColor_eq_of_le hst (he z)) hmatch
  exact ⟨e, fun z t => he t z⟩

theorem stable_joint_of_bisimulation {n k : ℕ} {G H : Graph n}
    (R : (Fin k → Fin n) → (Fin k → Fin n) → Prop)
    (atomic : ∀ v w, R v w → tupleColor .joint k G 0 v = tupleColor .joint k H 0 w)
    (extend : ∀ v w, R v w → ∃ e : Fin n ≃ Fin n, ∀ z i,
      R (Function.update v i z) (Function.update w i (e z)))
    {v w : Fin k → Fin n} (hR : R v w) : Stable .joint k G H v w := by
  intro t
  induction t generalizing v w with
  | zero => exact atomic v w hR
  | succ t ih =>
    obtain ⟨e, he⟩ := extend v w hR
    apply Prod.ext (ih hR)
    apply multiset_match_of_equiv _ _ e
    intro z
    funext i
    exact ih (he z i)

theorem stable_separate_of_bisimulation {n k : ℕ} {G H : Graph n}
    (R : (Fin k → Fin n) → (Fin k → Fin n) → Prop)
    (atomic : ∀ v w, R v w →
      tupleColor .separate k G 0 v = tupleColor .separate k H 0 w)
    (extend : ∀ v w, R v w → ∀ i, ∃ e : Fin n ≃ Fin n, ∀ z,
      R (Function.update v i z) (Function.update w i (e z)))
    {v w : Fin k → Fin n} (hR : R v w) : Stable .separate k G H v w := by
  intro t
  induction t generalizing v w with
  | zero => exact atomic v w hR
  | succ t ih =>
    apply Prod.ext (ih hR)
    funext i
    obtain ⟨e, he⟩ := extend v w hR i
    apply multiset_match_of_equiv _ _ e
    intro z
    exact ih (he z)

end WLTime

namespace WLTime

def permuteColor (c : Convention) (k : ℕ) (π : Equiv.Perm (Fin k)) :
    (t : ℕ) → Color c k t → Color c k t
  | 0, col => (fun i j => col.1 (π i) (π j), fun i j => col.2 (π i) (π j))
  | t + 1, col => match c with
    | .joint => (permuteColor .joint k π t col.1,
        col.2.map (fun vector i => permuteColor .joint k π t (vector (π i))))
    | .separate => (permuteColor .separate k π t col.1,
        fun i => (col.2 (π i)).map (permuteColor .separate k π t))

theorem tupleColor_permute {n k : ℕ} (c : Convention) (G : Graph n)
    (π : Equiv.Perm (Fin k)) (t : ℕ) (v : Fin k → Fin n) :
    tupleColor c k G t (v ∘ π) = permuteColor c k π t (tupleColor c k G t v) := by
  induction t generalizing v with
  | zero => rfl
  | succ t ih =>
    cases c with
    | joint =>
      apply Prod.ext (ih v)
      dsimp only [tupleColor, permuteColor]
      rw [Multiset.map_map]
      apply Multiset.map_congr rfl
      intro z _
      funext i
      rw [← Function.update_comp_eq_of_injective v π.injective i z]
      exact ih (Function.update v (π i) z)
    | separate =>
      apply Prod.ext (ih v)
      funext i
      dsimp only [tupleColor, permuteColor]
      rw [Multiset.map_map]
      apply Multiset.map_congr rfl
      intro z _
      rw [← Function.update_comp_eq_of_injective v π.injective i z]
      exact ih (Function.update v (π i) z)

theorem Stable.permute {n k : ℕ} {c : Convention} {G H : Graph n}
    {v w : Fin k → Fin n} (h : Stable c k G H v w) (π : Equiv.Perm (Fin k)) :
    Stable c k G H (v ∘ π) (w ∘ π) := by
  intro t
  rw [tupleColor_permute, tupleColor_permute, h t]

end WLTime

namespace WLTime

abbrev Position (K n : ℕ) := Fin K → Option (Fin n × Fin n)

def Position.Sub {K n : ℕ} (P Q : Position K n) : Prop :=
  ∀ i, P i = none ∨ P i = Q i

def Position.PartialIso {K n : ℕ} (G H : Graph n) (P : Position K n) : Prop :=
  ∀ i j x y u v, P i = some (x, y) → P j = some (u, v) →
    (x = u ↔ y = v) ∧ G.adj x u = H.adj y v

structure GameInvariant {n : ℕ} (G H : Graph n) (K : ℕ) where
  safe : Position K n → Prop
  forget : ∀ {P Q}, safe Q → P.Sub Q → safe P
  atomic : ∀ {P}, safe P → P.PartialIso G H
  extend : ∀ {P}, safe P → ∀ i, P i = none →
    ∃ e : Fin n ≃ Fin n, ∀ z, safe (Function.update P i (some (z, e z)))

def Wins {n K : ℕ} (G H : Graph n) (P : Position K n) : Prop :=
  ∃ I : GameInvariant G H K, I.safe P

theorem Wins.forget {n K : ℕ} {G H : Graph n} {P Q : Position K n}
    (h : Wins G H Q) (hPQ : P.Sub Q) : Wins G H P := by
  obtain ⟨I, hI⟩ := h
  exact ⟨I, I.forget hI hPQ⟩

theorem Wins.atomic {n K : ℕ} {G H : Graph n} {P : Position K n}
    (h : Wins G H P) : P.PartialIso G H := by
  obtain ⟨I, hI⟩ := h
  exact I.atomic hI

theorem Wins.extend {n K : ℕ} {G H : Graph n} {P : Position K n}
    (h : Wins G H P) (i : Fin K) (hi : P i = none) :
    ∃ e : Fin n ≃ Fin n, ∀ z, Wins G H (Function.update P i (some (z, e z))) := by
  obtain ⟨I, hI⟩ := h
  obtain ⟨e, he⟩ := I.extend hI i hi
  exact ⟨e, fun z => ⟨I, he z⟩⟩

def Marks {n K k : ℕ} (P : Position K n) (slot : Fin k → Fin K)
    (v w : Fin k → Fin n) : Prop := ∀ i, P (slot i) = some (v i, w i)

private theorem injective_update_fresh {α : Type uα} {β : Type uβ} [DecidableEq α]
    {f : α → β} (hf : Function.Injective f) (i : α) (b : β)
    (fresh : ∀ a, f a ≠ b) : Function.Injective (Function.update f i b) := by
  intro a c h
  by_cases ha : a = i
  · subst a
    by_cases hc : c = i
    · exact hc.symm
    · simp only [Function.update_self, Function.update_of_ne hc] at h
      exact (fresh c h.symm).elim
  · by_cases hc : c = i
    · subst c
      simp only [Function.update_self, Function.update_of_ne ha] at h
      exact (fresh a h).elim
    · simp only [Function.update_of_ne ha, Function.update_of_ne hc] at h
      exact hf h

private theorem exists_fresh_slot {k K : ℕ} (hk : k < K) (slot : Fin k → Fin K) :
    ∃ j, ∀ i, slot i ≠ j := by
  by_contra! h
  have hc := Fintype.card_le_of_surjective slot h
  simp only [Fintype.card_fin] at hc
  omega

private theorem atomic_of_wins_marks {n K k : ℕ} {G H : Graph n}
    {P : Position K n} {slot : Fin k → Fin K} {v w : Fin k → Fin n}
    (hP : Wins G H P) (hm : Marks P slot v w) (c : Convention) :
    tupleColor c k G 0 v = tupleColor c k H 0 w := by
  apply Prod.ext
  · funext i j
    change decide (v i = v j) = decide (w i = w j)
    exact decide_eq_decide.mpr (hP.atomic (slot i) (slot j)
      (v i) (w i) (v j) (w j) (hm i) (hm j)).1
  · funext i j
    exact (hP.atomic (slot i) (slot j) (v i) (w i) (v j) (w j) (hm i) (hm j)).2

theorem joint_color_of_wins {n K k : ℕ} {G H : Graph n} (hk : k < K)
    (t : ℕ) {P : Position K n} {slot : Fin k → Fin K}
    (hs : Function.Injective slot) {v w : Fin k → Fin n}
    (hP : Wins G H P) (hm : Marks P slot v w) :
    tupleColor .joint k G t v = tupleColor .joint k H t w := by
  classical
  induction t generalizing P slot v w with
  | zero => exact atomic_of_wins_marks hP hm .joint
  | succ t ih =>
    obtain ⟨j, hj⟩ := exists_fresh_slot hk slot
    let P₀ : Position K n := fun l => if l ∈ Set.range slot then P l else none
    have h₀ : Wins G H P₀ := hP.forget (fun l => by
      by_cases hl : l ∈ Set.range slot
      · exact Or.inr (ite_eq_left hl)
      · exact Or.inl (ite_eq_right hl))
    have h₀j : P₀ j = none := by
      simp only [P₀, Set.mem_range]
      exact ite_eq_right (by rintro ⟨i, hi⟩; exact hj i hi)
    obtain ⟨e, he⟩ := h₀.extend j h₀j
    apply Prod.ext (ih hs hP hm)
    apply multiset_match_of_equiv _ _ e
    intro z
    funext i
    apply ih (injective_update_fresh hs i j hj) (he z)
    intro l
    by_cases hl : l = i
    · subst l
      simp only [Function.update_self]
    · simp only [Function.update_of_ne hl, Function.update_of_ne (hj l), P₀]
      rw [ite_eq_left (Set.mem_range_self l)]
      exact hm l

theorem separate_color_of_wins {n K k : ℕ} {G H : Graph n}
    (t : ℕ) {P : Position K n} {slot : Fin k → Fin K}
    (hs : Function.Injective slot) {v w : Fin k → Fin n}
    (hP : Wins G H P) (hm : Marks P slot v w) :
    tupleColor .separate k G t v = tupleColor .separate k H t w := by
  classical
  induction t generalizing P v w with
  | zero => exact atomic_of_wins_marks hP hm .separate
  | succ t ih =>
    apply Prod.ext (ih hP hm)
    funext i
    let P₀ := Function.update P (slot i) none
    have h₀ : Wins G H P₀ := hP.forget (fun l => by
      by_cases hl : l = slot i <;> simp [P₀, hl])
    obtain ⟨e, he⟩ := h₀.extend (slot i) (Function.update_self _ _ _)
    apply multiset_match_of_equiv _ _ e
    intro z
    apply ih (he z)
    intro l
    by_cases hl : l = i
    · subst l
      simp only [Function.update_self]
    · have hl' : slot l ≠ slot i := fun heq => hl (hs heq)
      simp only [Function.update_of_ne hl, Function.update_of_ne hl', P₀]
      exact hm l

end WLTime

namespace WLTime

theorem Position.Sub.refl {n K : ℕ} (P : Position K n) : P.Sub P :=
  fun _ => Or.inr rfl

theorem Position.Sub.trans {n K : ℕ} {P Q R : Position K n}
    (hPQ : P.Sub Q) (hQR : Q.Sub R) : P.Sub R := by
  intro i
  rcases hPQ i with hi | hi
  · exact Or.inl hi
  · rcases hQR i with hj | hj
    · exact Or.inl (hi.trans hj)
    · exact Or.inr (hi.trans hj)

theorem Position.Sub.mark {n K : ℕ} {P Q : Position K n} (hPQ : P.Sub Q)
    {i : Fin K} {x y : Fin n} (hi : P i = some (x, y)) : Q i = some (x, y) := by
  rcases hPQ i with h | h
  · rw [hi] at h
    contradiction
  · exact h.symm.trans hi

theorem wins_matching {n K k : ℕ} {G H : Graph n} {P : Position K n}
    (hP : Wins G H P) (slot : Fin k → Fin K) (hs : Function.Injective slot)
    (hfree : ∀ i, P (slot i) = none) :
    ∃ e : (Fin k → Fin n) ≃ (Fin k → Fin n), ∀ v,
      ∃ Q, Wins G H Q ∧ P.Sub Q ∧ Marks Q slot v (e v) := by
  classical
  induction k generalizing P with
  | zero =>
    refine ⟨Equiv.refl _, fun v => ⟨P, hP, Position.Sub.refl P, ?_⟩⟩
    intro i
    exact Fin.elim0 i
  | succ k ih =>
    obtain ⟨e, he⟩ := hP.extend (slot 0) (hfree 0)
    have hex (z : Fin n) := ih (he z) (slot ∘ Fin.succ)
      (hs.comp (Fin.succ_injective k)) (fun i => by
        have hi : slot i.succ ≠ slot 0 := fun h => Fin.succ_ne_zero i (hs h)
        simpa only [Function.comp_apply, Function.update_of_ne hi] using hfree i.succ)
    choose es hes using hex
    let F : (Fin (k + 1) → Fin n) ≃ (Fin (k + 1) → Fin n) :=
      (Fin.consEquiv (fun _ : Fin (k + 1) => Fin n)).symm |>.trans
        ((Equiv.prodCongrRight es).trans
          ((Equiv.prodCongr e (Equiv.refl _)).trans
            (Fin.consEquiv (fun _ : Fin (k + 1) => Fin n))))
    refine ⟨F, fun v => ?_⟩
    obtain ⟨Q, hQ, hSQ, hm⟩ := hes (v 0) (v ∘ Fin.succ)
    refine ⟨Q, hQ, ?_, ?_⟩
    · apply Position.Sub.trans (Q := Function.update P (slot 0) (some (v 0, e (v 0)))) _ hSQ
      intro i
      by_cases hi : i = slot 0
      · exact Or.inl (hi ▸ hfree 0)
      · exact Or.inr (Function.update_of_ne hi _ _).symm
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hSQ.mark (Function.update_self _ _ _)
      · exact hm j

theorem equivalent_joint_of_wins {n K k : ℕ} {G H : Graph n} (hk : k < K)
    (h : Wins G H (fun _ : Fin K => none)) : Equivalent .joint k G H := by
  let slot : Fin k → Fin K := fun i => ⟨i.val, lt_trans i.isLt hk⟩
  have hs : Function.Injective slot := fun _ _ heq => Fin.ext (congrArg (fun i : Fin K => i.val) heq)
  obtain ⟨e, he⟩ := wins_matching h slot hs (fun _ => rfl)
  intro t
  apply multiset_match_of_equiv _ _ e
  intro v
  obtain ⟨Q, hQ, _, hm⟩ := he v
  exact joint_color_of_wins hk t hs hQ hm

theorem equivalent_separate_of_wins {n K k : ℕ} {G H : Graph n} (hk : k ≤ K)
    (h : Wins G H (fun _ : Fin K => none)) : Equivalent .separate k G H := by
  let slot : Fin k → Fin K := fun i => ⟨i.val, lt_of_lt_of_le i.isLt hk⟩
  have hs : Function.Injective slot := fun _ _ heq => Fin.ext (congrArg (fun i : Fin K => i.val) heq)
  obtain ⟨e, he⟩ := wins_matching h slot hs (fun _ => rfl)
  intro t
  apply multiset_match_of_equiv _ _ e
  intro v
  obtain ⟨Q, hQ, _, hm⟩ := he v
  exact separate_color_of_wins t hs hQ hm

end WLTime

namespace WLTime

def completePosition {n K : ℕ} (v w : Fin K → Fin n) : Position K n :=
  fun i => some (v i, w i)

theorem atomic_of_stable {n k : ℕ} {c : Convention} {G H : Graph n}
    {v w : Fin k → Fin n} (h : Stable c k G H v w) (i j : Fin k) :
    (v i = v j ↔ w i = w j) ∧ G.adj (v i) (v j) = H.adj (w i) (w j) := by
  have h₀ := h 0
  constructor
  · exact decide_eq_decide.mp (congrFun (congrFun (congrArg Prod.fst h₀) i) j)
  · exact congrFun (congrFun (congrArg Prod.snd h₀) i) j

theorem partialIso_of_stable {n k : ℕ} {c : Convention} {G H : Graph n}
    {v w : Fin k → Fin n} (h : Stable c k G H v w) {P : Position k n}
    (hP : P.Sub (completePosition v w)) : P.PartialIso G H := by
  intro i j x y u z hi hj
  have hi' := Prod.mk.inj (Option.some.inj (hP.mark hi))
  have hj' := Prod.mk.inj (Option.some.inj (hP.mark hj))
  change v i = x ∧ w i = y at hi'
  change v j = u ∧ w j = z at hj'
  rw [← hi'.1, ← hi'.2, ← hj'.1, ← hj'.2]
  exact atomic_of_stable h i j

theorem sub_complete_update {n k : ℕ} {v w : Fin k → Fin n} {P : Position k n}
    (hP : P.Sub (completePosition v w)) (i : Fin k) (x y : Fin n) :
    Position.Sub (Function.update P i (some (x, y)))
      (completePosition (Function.update v i x) (Function.update w i y)) := by
  intro j
  by_cases hj : j = i
  · subst j
    right
    simp only [Function.update_self, completePosition]
  · simpa only [Function.update_of_ne hj, completePosition] using hP j

theorem wins_of_stable_separate {n k : ℕ} {G H : Graph n} {v w : Fin k → Fin n}
    (h : Stable .separate k G H v w) {P : Position k n}
    (hP : P.Sub (completePosition v w)) : Wins G H P := by
  let I : GameInvariant G H k := {
    safe := fun Q => ∃ a b, Stable .separate k G H a b ∧ Q.Sub (completePosition a b)
    forget := by
      rintro Q R ⟨a, b, hab, hR⟩ hQR
      exact ⟨a, b, hab, hQR.trans hR⟩
    atomic := by
      rintro Q ⟨a, b, hab, hQ⟩
      exact partialIso_of_stable hab hQ
    extend := by
      rintro Q ⟨a, b, hab, hQ⟩ i _
      obtain ⟨e, he⟩ := stable_separate_extension hab i
      exact ⟨e, fun z => ⟨_, _, he z, sub_complete_update hQ i z (e z)⟩⟩ }
  exact ⟨I, v, w, h, hP⟩

theorem separate_stable_iff_wins {n k : ℕ} {G H : Graph n} {v w : Fin k → Fin n} :
    Stable .separate k G H v w ↔ Wins G H (completePosition v w) := by
  constructor
  · intro h
    exact wins_of_stable_separate h (Position.Sub.refl _)
  · intro h t
    exact separate_color_of_wins t Function.injective_id h (fun _ => rfl)

theorem wins_of_equivalent_separate {n k : ℕ} {G H : Graph n} (hn : 0 < n)
    (h : Equivalent .separate k G H) : Wins G H (fun _ : Fin k => none) := by
  obtain ⟨e, he⟩ := equivalent_stable_matching h
  let v : Fin k → Fin n := fun _ => ⟨0, hn⟩
  exact wins_of_stable_separate (he v) (fun _ => Or.inl rfl)

theorem separate_equivalent_iff_wins {n k : ℕ} {G H : Graph n} (hn : 0 < n) :
    Equivalent .separate k G H ↔ Wins G H (fun _ : Fin k => none) :=
  ⟨wins_of_equivalent_separate hn, equivalent_separate_of_wins le_rfl⟩

end WLTime

namespace WLTime

private theorem factor_injective {α : Type uα} {β : Type uβ} [Finite α] {f g : α → β}
    (hg : Function.Injective g) (hcover : ∀ a, ∃ b, f b = g a) :
    ∃ π : Equiv.Perm α, ∀ a, f (π a) = g a := by
  classical
  choose p hp using hcover
  have hinj : Function.Injective p := by
    intro a b hab
    apply hg
    rw [← hp a, ← hp b, hab]
  exact ⟨Equiv.ofBijective p ⟨hinj, Finite.surjective_of_injective hinj⟩, hp⟩

private theorem projection_factor {k : ℕ} (i : Fin (k + 1))
    (τ : Fin k → Fin (k + 1)) (hτ : Function.Injective τ) :
    (∃ π : Equiv.Perm (Fin k), ∀ b, i.succAbove (π b) = τ b) ∨
    ∃ a, ∃ π : Equiv.Perm (Fin k),
      ∀ b, Function.update i.succAbove a i (π b) = τ b := by
  classical
  by_cases hi : ∃ a, τ a = i
  · right
    obtain ⟨b, hb⟩ := hi
    obtain ⟨o, ho⟩ := exists_fresh_slot (Nat.lt_succ_self k) τ
    have hoi : o ≠ i := by
      intro h
      exact ho b (hb.trans h.symm)
    obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hoi
    refine ⟨a, factor_injective hτ ?_⟩
    intro d
    by_cases hd : τ d = i
    · exact ⟨a, (Function.update_self _ _ _).trans hd.symm⟩
    · obtain ⟨c, hc⟩ := Fin.exists_succAbove_eq hd
      have hca : c ≠ a := by
        intro h
        exact ho d (hc.symm.trans (h ▸ ha))
      exact ⟨c, (Function.update_of_ne hca _ _).trans hc⟩
  · left
    apply factor_injective hτ
    intro a
    apply Fin.exists_succAbove_eq
    intro h
    exact hi ⟨a, h⟩

def JointFull {n k : ℕ} (G H : Graph n) (v w : Fin (k + 1) → Fin n) : Prop :=
  ∀ τ : Fin k ↪ Fin (k + 1), Stable .joint k G H (v ∘ τ) (w ∘ τ)

private theorem update_projection {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq α] [DecidableEq β]
    (u : β → γ) (σ : α → β) (i : β) (fresh : ∀ a, σ a ≠ i) (a : α) (z : γ) :
    Function.update u i z ∘ Function.update σ a i = Function.update (u ∘ σ) a z := by
  funext b
  by_cases hb : b = a
  · subst b
    simp only [Function.comp_apply, Function.update_self]
  · simp only [Function.comp_apply, Function.update_of_ne hb, Function.update_of_ne (fresh b)]

theorem joint_full_extend {n k : ℕ} {G H : Graph n} {v w : Fin (k + 1) → Fin n}
    (i : Fin (k + 1))
    (h : Stable .joint k G H (v ∘ i.succAbove) (w ∘ i.succAbove)) :
    ∃ e : Fin n ≃ Fin n, ∀ z,
      JointFull G H (Function.update v i z) (Function.update w i (e z)) := by
  classical
  obtain ⟨e, he⟩ := stable_joint_extension h
  refine ⟨e, fun z τ => ?_⟩
  rcases projection_factor i τ τ.injective with ⟨π, hπ⟩ | ⟨a, π, hπ⟩
  · have hv : Function.update v i z ∘ τ = (v ∘ i.succAbove) ∘ π := by
      funext b
      simp only [Function.comp_apply, ← hπ b, Function.update_of_ne (Fin.succAbove_ne i (π b))]
    have hw : Function.update w i (e z) ∘ τ = (w ∘ i.succAbove) ∘ π := by
      funext b
      simp only [Function.comp_apply, ← hπ b, Function.update_of_ne (Fin.succAbove_ne i (π b))]
    rw [hv, hw]
    exact h.permute π
  · have hτ : (τ : Fin k → Fin (k + 1)) = Function.update i.succAbove a i ∘ π :=
      funext (fun b => (hπ b).symm)
    rw [hτ, ← Function.comp_assoc, ← Function.comp_assoc,
      update_projection v i.succAbove i (Fin.succAbove_ne i),
      update_projection w i.succAbove i (Fin.succAbove_ne i)]
    exact (he z a).permute π

private theorem exists_third_slot {k : ℕ} (hk : 2 ≤ k) (i j : Fin (k + 1)) :
    ∃ o, o ≠ i ∧ o ≠ j := by
  classical
  have hc : ({i, j} : Finset (Fin (k + 1))).card < (Finset.univ : Finset (Fin (k + 1))).card := by
    have h := Finset.card_insert_le i ({j} : Finset (Fin (k + 1)))
    simp only [Finset.card_singleton, Finset.card_univ, Fintype.card_fin] at *
    omega
  obtain ⟨o, _, ho⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  refine ⟨o, ?_⟩
  simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using ho

theorem partialIso_of_jointFull {n k : ℕ} {G H : Graph n} (hk : 2 ≤ k)
    {v w : Fin (k + 1) → Fin n} (h : JointFull G H v w) {P : Position (k + 1) n}
    (hP : P.Sub (completePosition v w)) : P.PartialIso G H := by
  intro i j x y u z hi hj
  have hi' := Prod.mk.inj (Option.some.inj (hP.mark hi))
  have hj' := Prod.mk.inj (Option.some.inj (hP.mark hj))
  change v i = x ∧ w i = y at hi'
  change v j = u ∧ w j = z at hj'
  rw [← hi'.1, ← hi'.2, ← hj'.1, ← hj'.2]
  obtain ⟨o, hoi, hoj⟩ := exists_third_slot hk i j
  obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hoi.symm
  obtain ⟨b, hb⟩ := Fin.exists_succAbove_eq hoj.symm
  have hab := atomic_of_stable (h o.succAboveEmb) a b
  simpa only [Function.comp_apply, Fin.succAboveEmb_apply, ha, hb] using hab

end WLTime

namespace WLTime

theorem wins_of_jointFull {n k : ℕ} {G H : Graph n} (hk : 2 ≤ k)
    {v w : Fin (k + 1) → Fin n} (h : JointFull G H v w) {P : Position (k + 1) n}
    (hP : P.Sub (completePosition v w)) : Wins G H P := by
  let I : GameInvariant G H (k + 1) := {
    safe := fun Q => ∃ a b, JointFull G H a b ∧ Q.Sub (completePosition a b)
    forget := by
      rintro Q R ⟨a, b, hab, hR⟩ hQR
      exact ⟨a, b, hab, hQR.trans hR⟩
    atomic := by
      rintro Q ⟨a, b, hab, hQ⟩
      exact partialIso_of_jointFull hk hab hQ
    extend := by
      rintro Q ⟨a, b, hab, hQ⟩ i _
      obtain ⟨e, he⟩ := joint_full_extend i (hab i.succAboveEmb)
      exact ⟨e, fun z => ⟨_, _, he z, sub_complete_update hQ i z (e z)⟩⟩ }
  exact ⟨I, v, w, h, hP⟩

def sparePosition {n k : ℕ} (v w : Fin k → Fin n) : Position (k + 1) n :=
  Fin.snoc (fun i => some (v i, w i)) none

theorem wins_of_stable_joint {n k : ℕ} {G H : Graph n} (hn : 0 < n) (hk : 2 ≤ k)
    {v w : Fin k → Fin n} (h : Stable .joint k G H v w) :
    Wins G H (sparePosition v w) := by
  let z : Fin n := ⟨0, hn⟩
  let v' : Fin (k + 1) → Fin n := Fin.snoc v z
  let w' : Fin (k + 1) → Fin n := Fin.snoc w z
  have hv : v' ∘ (Fin.last k).succAbove = v := by
    funext i
    simp [v', Fin.succAbove_last]
  have hw : w' ∘ (Fin.last k).succAbove = w := by
    funext i
    simp [w', Fin.succAbove_last]
  obtain ⟨e, he⟩ := joint_full_extend (Fin.last k) (show Stable .joint k G H
    (v' ∘ (Fin.last k).succAbove) (w' ∘ (Fin.last k).succAbove) from hv ▸ hw ▸ h)
  apply wins_of_jointFull hk (he z)
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · left
    exact Fin.snoc_last _ _
  · right
    simp only [sparePosition, Fin.snoc_castSucc, completePosition,
      Function.update_of_ne (Fin.castSucc_ne_last j), v', w']

theorem joint_stable_iff_wins {n k : ℕ} {G H : Graph n} (hn : 0 < n) (hk : 2 ≤ k)
    {v w : Fin k → Fin n} :
    Stable .joint k G H v w ↔ Wins G H (sparePosition v w) := by
  constructor
  · exact wins_of_stable_joint hn hk
  · intro h t
    apply joint_color_of_wins (Nat.lt_succ_self k) t (Fin.castSucc_injective k) h
    intro i
    exact Fin.snoc_castSucc _ _ _

theorem wins_of_equivalent_joint {n k : ℕ} {G H : Graph n} (hn : 0 < n) (hk : 2 ≤ k)
    (h : Equivalent .joint k G H) : Wins G H (fun _ : Fin (k + 1) => none) := by
  obtain ⟨e, he⟩ := equivalent_stable_matching h
  let v : Fin k → Fin n := fun _ => ⟨0, hn⟩
  exact (wins_of_stable_joint hn hk (he v)).forget (fun _ => Or.inl rfl)

theorem joint_equivalent_iff_wins {n k : ℕ} {G H : Graph n} (hn : 0 < n) (hk : 2 ≤ k) :
    Equivalent .joint k G H ↔ Wins G H (fun _ : Fin (k + 1) => none) :=
  ⟨wins_of_equivalent_joint hn hk, equivalent_joint_of_wins (Nat.lt_succ_self k)⟩

end WLTime

namespace WLTime

noncomputable def Graph.degree {n : ℕ} (G : Graph n) (x : Fin n) : ℕ :=
  Fintype.card {z : Fin n // G.adj x z = true}

theorem Wins.neighborhood_bijection {n K : ℕ} {G H : Graph n} (hK : 2 ≤ K)
    {P : Position K n} (hP : Wins G H P) {i : Fin K} {x y : Fin n}
    (hi : P i = some (x, y)) :
    ∃ e : Fin n ≃ Fin n, e x = y ∧ ∀ z, G.adj x z = H.adj y (e z) := by
  classical
  obtain ⟨j, hj⟩ := exists_fresh_slot (show 1 < K by omega) (fun _ : Fin 1 => i)
  have hij : i ≠ j := hj 0
  let Q : Position K n := fun a => if a = i then P a else none
  have hQ : Wins G H Q := hP.forget (fun a => by
    by_cases ha : a = i
    · right; exact ite_eq_left ha
    · left; exact ite_eq_right ha)
  have hQj : Q j = none := ite_eq_right hij.symm
  obtain ⟨e, he⟩ := hQ.extend j hQj
  have hat (z : Fin n) := (he z).atomic i j x y z (e z)
    (by simp only [Function.update_of_ne hij, Q, hi, ite_true])
    (Function.update_self _ _ _)
  exact ⟨e, ((hat x).1.mp rfl).symm, fun z => (hat z).2⟩

theorem Wins.degree_eq {n K : ℕ} {G H : Graph n} (hK : 2 ≤ K)
    {P : Position K n} (hP : Wins G H P) {i : Fin K} {x y : Fin n}
    (hi : P i = some (x, y)) : G.degree x = H.degree y := by
  obtain ⟨e, _, he⟩ := Wins.neighborhood_bijection hK hP hi
  apply Fintype.card_congr
  exact Equiv.subtypeEquiv e (fun z => by rw [he z])

end WLTime

end OAI
