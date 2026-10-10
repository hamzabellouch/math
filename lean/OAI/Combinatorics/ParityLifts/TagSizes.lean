import OAI.Combinatorics.ParityLifts.BagTrees

namespace OAI

namespace ParityWL

open scoped BigOperators

section TagSizes

open scoped Classical

variable {I : Type} [Fintype I]

lemma sum_split_at (a : I) (f : I → Bit) :
    ∑ i, f i = f a + ∑ i : {i : I // i ≠ a}, f i := by
  have hs := (Fintype.sum_subtype_add_sum_subtype (fun i => i = a) f).symm
  simp only [Fintype.sum_unique] at hs
  simpa only [(default : {i : I // i = a}).property] using hs

noncomputable def sumFiberEquiv (a : I) (b : Bit) :
    {f : I → Bit // ∑ i, f i = b} ≃ ({i : I // i ≠ a} → Bit) where
  toFun f i := f.1 i
  invFun f := ⟨fun i => if h : i = a then b - ∑ j, f j else f ⟨i, h⟩, by
    rw [sum_split_at a]
    have he : (∑ i : {i : I // i ≠ a},
        if h : (i : I) = a then b - ∑ j, f j else f ⟨i, h⟩) = ∑ i, f i := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [dite_eq_right i.property]
    rw [he]
    rw [dite_eq_left rfl]
    exact sub_add_cancel b (∑ j, f j)⟩
  left_inv := by
    intro f
    apply Subtype.ext
    funext i
    by_cases h : i = a
    · subst i
      dsimp only
      rw [dite_eq_left rfl]
      have hf := f.2
      rw [sum_split_at a] at hf
      exact eq_sub_of_add_eq hf |>.symm
    · simp [h]
  right_inv := by
    intro f
    funext i
    simp [i.property]

lemma card_sumFiber (a : I) (b : Bit) :
    Fintype.card {f : I → Bit // ∑ i, f i = b} = 2 ^ (Fintype.card I - 1) := by
  rw [Fintype.card_congr (sumFiberEquiv a b), Fintype.card_fun, ZMod.card]
  congr 1
  simp [Fintype.card_subtype_compl]

lemma card_tag {A : Type} [Fintype A] (T : SimpleGraph A) (b : A → Bit)
    (a : A) (h : (T.neighborSet a).Nonempty) :
    Fintype.card (Tag T b a) = 2 ^ (Fintype.card (T.neighborSet a) - 1) := by
  classical
  obtain ⟨i, hi⟩ := h
  exact Fintype.card_congr (sumFiberEquiv (⟨i, hi⟩ : T.neighborSet a) (b a)) |>.trans (by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_subtype_compl, Fintype.card_subtype_eq])

lemma template_positive_degree {t : ℕ} (ht : 2 ≤ t) (a : TemplateVertex t) :
    ((template t).neighborSet a).Nonempty := by
  cases a with
  | inl i =>
    by_cases hi : i.val = 0
    · refine ⟨.inl ⟨1, by omega⟩, ?_⟩
      change i ≠ ⟨1, by omega⟩
      intro h
      have hh := congrArg Fin.val h
      change i.val = 1 at hh
      omega
    · refine ⟨.inl ⟨0, by omega⟩, ?_⟩
      change i ≠ ⟨0, by omega⟩
      intro h
      exact hi (congrArg Fin.val h)
  | inr h => exact ⟨.inl h.1.1.1.1, Or.inl rfl⟩

lemma lift_card_eq {A V : Type} [Fintype A] [Fintype V]
    (T : SimpleGraph A) (G : SimpleGraph V) (τ : G →g T) (b c : A → Bit)
    (h : ∀ a, (T.neighborSet a).Nonempty) :
    Fintype.card (LiftVertex T G τ b) = Fintype.card (LiftVertex T G τ c) := by
  simp only [LiftVertex, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro u _
  rw [card_tag T b (τ u) (h _), card_tag T c (τ u) (h _)]

lemma choice_lifts_equal_order {t : ℕ} (ht : 2 ≤ t) (C : ChoiceSystem t) :
    Fintype.card (LiftVertex (template t) (baseGraph C) (baseProjection C) (fun _ => 0)) =
      Fintype.card (LiftVertex (template t) (baseGraph C) (baseProjection C) (starParity t)) :=
  lift_card_eq _ _ _ _ _ (template_positive_degree ht)

noncomputable def mainPairEquiv (t : ℕ) : MainPair t ≃ ((j : Fin t) × Fin j.val) where
  toFun p := ⟨p.1.2, ⟨p.1.1.val, p.2⟩⟩
  invFun p := ⟨(⟨p.2.val, p.2.isLt.trans p.1.isLt⟩, p.1), p.2.isLt⟩
  left_inv _p := rfl
  right_inv _p := rfl

lemma card_mainPair (t : ℕ) : Fintype.card (MainPair t) = t.choose 2 := by
  rw [Fintype.card_congr (mainPairEquiv t), Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun n => n), Finset.sum_range_id, Nat.choose_two_right]

lemma card_avoid_two {J : Type} [Fintype J] [DecidableEq J] (a b : J) (hab : a ≠ b) :
    Fintype.card {i : J // i ≠ a ∧ i ≠ b} = Fintype.card J - 2 := by
  have he : Fintype.card {i : J // i = a ∨ i = b} = 2 := by
    have h := Fintype.card_coe ({a, b} : Finset J)
    simpa [hab] using h
  have h := Fintype.card_subtype_compl (fun i : J => i = a ∨ i = b)
  simpa only [not_or, he] using h

noncomputable def helperSigmaEquiv (t : ℕ) :
    Helper t ≃ ((p : MainPair t) × {i : Fin t // i ≠ p.1.1 ∧ i ≠ p.1.2}) where
  toFun h := ⟨h.1.1, ⟨h.1.2, h.2⟩⟩
  invFun h := ⟨(h.1, h.2.1), h.2.2⟩
  left_inv _h := rfl
  right_inv _h := rfl

lemma card_helper (t : ℕ) : Fintype.card (Helper t) = 3 * t.choose 3 := by
  rw [Fintype.card_congr (helperSigmaEquiv t), Fintype.card_sigma]
  have h : ∀ p : MainPair t,
      Fintype.card {i : Fin t // i ≠ p.1.1 ∧ i ≠ p.1.2} = t - 2 := by
    intro p
    simpa using card_avoid_two p.1.1 p.1.2 (ne_of_lt p.2)
  simp_rw [h]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, card_mainPair]
  simpa only [Nat.mul_comm] using (Nat.choose_succ_right_eq t 2).symm

abbrev OrderedPair (J : Type) [LT J] := {p : J × J // p.1 < p.2}

noncomputable def orderedPairEquiv {J : Type} [Fintype J] [LinearOrder J] :
    OrderedPair J ≃ MainPair (Fintype.card J) := by
  let e := (Fintype.orderIsoFinOfCardEq J rfl).symm
  exact
    { toFun := fun p => ⟨(e p.1.1, e p.1.2), e.strictMono p.2⟩
      invFun := fun p => ⟨(e.symm p.1.1, e.symm p.1.2), e.symm.strictMono p.2⟩
      left_inv := by intro p; apply Subtype.ext; simp
      right_inv := by intro p; apply Subtype.ext; simp }

lemma card_orderedPair {J : Type} [Fintype J] [LinearOrder J] :
    Fintype.card (OrderedPair J) = (Fintype.card J).choose 2 := by
  rw [Fintype.card_congr orderedPairEquiv, card_mainPair]

abbrev PairsThrough {t : ℕ} (i : Fin t) :=
  {p : MainPair t // i = p.1.1 ∨ i = p.1.2}

noncomputable def pairOther {t : ℕ} (i : Fin t) (p : PairsThrough i) :
    {j : Fin t // j ≠ i} :=
  if h : i = p.1.1.1 then
    ⟨p.1.1.2, fun he => (ne_of_lt p.1.2) (h.symm.trans he.symm)⟩
  else ⟨p.1.1.1, fun he => h he.symm⟩

lemma pairOther_injective {t : ℕ} (i : Fin t) : Function.Injective (pairOther i) := by
  intro p q hpq
  have he := congrArg Subtype.val hpq
  dsimp only [pairOther] at he
  apply Subtype.ext
  apply Subtype.ext
  by_cases hp : i = p.1.1.1 <;> by_cases hq : i = q.1.1.1
  · simp only [dite_eq_left hp, dite_eq_left hq] at he
    exact Prod.ext (hp.symm.trans hq) he
  · simp only [dite_eq_left hp, dite_eq_right hq] at he
    have hq' : i = q.1.1.2 := q.2.resolve_left hq
    have hlt := p.1.2
    have hlt' := q.1.2
    rw [← hp, he] at hlt
    rw [← hq'] at hlt'
    exact (lt_asymm hlt hlt').elim
  · simp only [dite_eq_right hp, dite_eq_left hq] at he
    have hp' : i = p.1.1.2 := p.2.resolve_left hp
    have hlt := p.1.2
    have hlt' := q.1.2
    rw [← hp'] at hlt
    rw [← hq, ← he] at hlt'
    exact (lt_asymm hlt hlt').elim
  · simp only [dite_eq_right hp, dite_eq_right hq] at he
    exact Prod.ext he ((p.2.resolve_left hp).symm.trans (q.2.resolve_left hq))

lemma card_pairsThrough_le {t : ℕ} (i : Fin t) :
    Fintype.card (PairsThrough i) ≤ t - 1 := by
  have h := Fintype.card_le_of_injective _ (pairOther_injective i)
  simpa [Fintype.card_subtype_compl] using h

noncomputable def helperThirdEquiv {t : ℕ} (i : Fin t) :
    {h : Helper t // i = h.1.2} ≃ OrderedPair {j : Fin t // j ≠ i} where
  toFun h := ⟨(⟨h.1.1.1.1.1, by simpa [h.2] using h.1.2.1.symm⟩,
    ⟨h.1.1.1.1.2, by simpa [h.2] using h.1.2.2.symm⟩), h.1.1.1.2⟩
  invFun p := ⟨⟨(⟨(p.1.1.1, p.1.2.1), p.2⟩, i),
    ⟨p.1.1.2.symm, p.1.2.2.symm⟩⟩, rfl⟩
  left_inv h := by apply Subtype.ext; apply Subtype.ext; exact Prod.ext rfl h.2
  right_inv p := rfl

noncomputable def helperEndpointEquiv {t : ℕ} (i : Fin t) :
    {h : Helper t // i = h.1.1.1.1 ∨ i = h.1.1.1.2} ≃
      ((p : PairsThrough i) × {j : Fin t // j ≠ p.1.1.1 ∧ j ≠ p.1.1.2}) where
  toFun h := ⟨⟨h.1.1.1, h.2⟩, ⟨h.1.1.2, h.1.2⟩⟩
  invFun p := ⟨⟨(p.1.1, p.2.1), p.2.2⟩, p.1.2⟩
  left_inv _h := rfl
  right_inv _p := rfl

lemma card_helpersIncident_le {t : ℕ} (i : Fin t) :
    Fintype.card {h : Helper t // helperIncident h i} ≤ 3 * (t - 1).choose 2 := by
  have he : Fintype.card {h : Helper t // i = h.1.1.1.1 ∨ i = h.1.1.1.2} ≤
      (t - 1) * (t - 2) := by
    rw [Fintype.card_congr (helperEndpointEquiv i), Fintype.card_sigma]
    have hc : ∀ p : PairsThrough i,
        Fintype.card {j : Fin t // j ≠ p.1.1.1 ∧ j ≠ p.1.1.2} = t - 2 :=
      fun p => by simpa using card_avoid_two p.1.1.1 p.1.1.2 (ne_of_lt p.1.2)
    simp_rw [hc]
    simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul] using
      Nat.mul_le_mul_right (t - 2) (card_pairsThrough_le i)
  have ht : Fintype.card {h : Helper t // i = h.1.2} = (t - 1).choose 2 := by
    rw [Fintype.card_congr (helperThirdEquiv i), card_orderedPair]
    simp [Fintype.card_subtype_compl]
  have h := Fintype.card_subtype_or
    (fun h : Helper t => i = h.1.1.1.1 ∨ i = h.1.1.1.2)
    (fun h : Helper t => i = h.1.2)
  have h' : Fintype.card {h : Helper t // helperIncident h i} ≤
      (t - 1) * (t - 2) + (t - 1).choose 2 := by
    have h0 : Fintype.card {h : Helper t // helperIncident h i} ≤
        Fintype.card {h : Helper t // i = h.1.1.1.1 ∨ i = h.1.1.1.2} +
          Fintype.card {h : Helper t // i = h.1.2} := by
      have hc := Fintype.card_congr (Equiv.subtypeEquivRight (fun h : Helper t =>
        show helperIncident h i ↔ (i = h.1.1.1.1 ∨ i = h.1.1.1.2) ∨ i = h.1.2
          from or_assoc.symm))
      exact hc.le.trans h
    exact h0.trans (Nat.add_le_add he ht.le)
  have hc := Nat.choose_succ_right_eq (t - 1) 1
  simp only [Nat.choose_one_right, Nat.sub_sub, Nat.reduceAdd] at hc
  omega

noncomputable def templateMainNeighbors {t : ℕ} (i : Fin t) :
    (template t).neighborSet (.inl i) ≃
      ({j : Fin t // j ≠ i} ⊕ {h : Helper t // helperIncident h i}) where
  toFun v := match v with
    | ⟨.inl j, h⟩ => .inl ⟨j, (show i ≠ j from h).symm⟩
    | ⟨.inr h, e⟩ => .inr ⟨h, e⟩
  invFun v := match v with
    | .inl j => ⟨.inl j.1, j.2.symm⟩
    | .inr h => ⟨.inr h.1, h.2⟩
  left_inv v := by rcases v with ⟨v, hv⟩; cases v <;> rfl
  right_inv v := by cases v <;> rfl

lemma template_degree_main_le {t : ℕ} (i : Fin t) :
    Fintype.card ((template t).neighborSet (.inl i)) ≤
      t - 1 + 3 * (t - 1).choose 2 := by
  rw [Fintype.card_congr (templateMainNeighbors i), Fintype.card_sum]
  have h : Fintype.card {j : Fin t // j ≠ i} = t - 1 := by
    simp [Fintype.card_subtype_compl]
  rw [h]
  exact Nat.add_le_add_left (card_helpersIncident_le i) _

lemma template_degree_helper {t : ℕ} (h : Helper t) :
    Fintype.card ((template t).neighborSet (.inr h)) = 3 := by
  let s : Finset (TemplateVertex t) :=
    {.inl h.1.1.1.1, .inl h.1.1.1.2, .inl h.1.2}
  have hs : ∀ v, v ∈ s ↔ v ∈ (template t).neighborSet (.inr h) := by
    intro v
    cases v <;> simp [s, template, templateAdj, helperIncident]
  rw [Fintype.card_of_finset' s hs]
  simp [s, ne_of_lt h.1.1.2, h.2.1.symm, h.2.2.symm]

lemma tag_main_bound {t : ℕ} (ht : 2 ≤ t) (b : TemplateVertex t → Bit)
    (i : Fin t) :
    Fintype.card (Tag (template t) b (.inl i)) ≤
      2 ^ (t - 2 + 3 * (t - 1).choose 2) := by
  rw [card_tag _ _ _ (template_positive_degree ht _)]
  apply Nat.pow_le_pow_right (by omega)
  have h := template_degree_main_le i
  omega

lemma tag_helper_card {t : ℕ} (ht : 2 ≤ t) (b : TemplateVertex t → Bit)
    (h : Helper t) : Fintype.card (Tag (template t) b (.inr h)) = 4 := by
  rw [card_tag _ _ _ (template_positive_degree ht _), template_degree_helper]
  norm_num

lemma choice_lift_order_bound {t : ℕ} (ht : 2 ≤ t) (C : ChoiceSystem t)
    (A : ℕ) (hA : C.SizeAtMost A) (b : TemplateVertex t → Bit) :
    Fintype.card (LiftVertex (template t) (baseGraph C) (baseProjection C) b) ≤
      A * orderFactor t := by
  let q := 2 ^ (t - 2 + 3 * (t - 1).choose 2)
  rw [Fintype.card_sigma]
  change (∑ u : BaseVertex C, Fintype.card (Tag (template t) b (baseType u))) ≤ _
  rw [Fintype.sum_sum_type]
  rw [Fintype.sum_sigma, Fintype.sum_sigma]
  change (∑ i : Fin t, ∑ _d : C.Domain i, Fintype.card (Tag (template t) b (.inl i))) +
    (∑ h : Helper t, ∑ _c : C.Label h.1.1, Fintype.card (Tag (template t) b (.inr h))) ≤ _
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  calc
    _ ≤ (∑ _i : Fin t, A * q) + (∑ _h : Helper t, A * 4) := by
      apply Nat.add_le_add
      · apply Finset.sum_le_sum
        intro i _
        exact Nat.mul_le_mul (hA.1 i) (tag_main_bound ht b i)
      · apply Finset.sum_le_sum
        intro h _
        rw [tag_helper_card ht]
        exact Nat.mul_le_mul_right 4 (hA.2 h.1.1)
    _ = A * orderFactor t := by
      simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_fin, card_helper]
      dsimp only [q, orderFactor]
      ring

end TagSizes

end ParityWL

end OAI
