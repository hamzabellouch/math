import OAI.Combinatorics.ParityLifts.Masses

namespace OAI

namespace ParityWL

open scoped BigOperators

section BaseLabels

open scoped Classical

variable {t : ℕ} (C : ChoiceSystem t)

lemma baseType_inl_iff (v : BaseVertex C) (i : Fin t) :
    baseType v = .inl i ↔ ∃ d : C.Domain i, v = .inl ⟨i, d⟩ := by
  cases v with
  | inl x =>
    rcases x with ⟨j, d⟩
    constructor
    · intro h
      have hj : j = i := Sum.inl.inj h
      subst j
      exact ⟨d, rfl⟩
    · rintro ⟨e, he⟩
      exact congrArg baseType he
  | inr x => simp [baseType]

lemma baseType_inr_iff (v : BaseVertex C) (h : Helper t) :
    baseType v = .inr h ↔ ∃ q : C.Label h.1.1, v = .inr ⟨h, q⟩ := by
  cases v with
  | inr x =>
    rcases x with ⟨j, d⟩
    constructor
    · intro h'
      have hj : j = h := Sum.inr.inj h'
      subst j
      exact ⟨d, rfl⟩
    · rintro ⟨e, he⟩
      exact congrArg baseType he
  | inl x => simp [baseType]

lemma base_main_label (p : MainPair t) (d : C.Domain p.1.1) (e : C.Domain p.1.2)
    (h : (baseGraph C).Adj (.inl ⟨p.1.1, d⟩) (.inl ⟨p.1.2, e⟩)) :
    C.leftLabel p d = C.rightLabel p e := by
  have forward : ∀ (p' : MainPair t) (d' : C.Domain p'.1.1) (e' : C.Domain p'.1.2),
      (.inl ⟨p'.1.1, d'⟩ : BaseVertex C) = .inl ⟨p.1.1, d⟩ →
      (.inl ⟨p'.1.2, e'⟩ : BaseVertex C) = .inl ⟨p.1.2, e⟩ →
      C.leftLabel p' d' = C.rightLabel p' e' → C.leftLabel p d = C.rightLabel p e := by
    intro p' d' e' h0 h1 hlabel
    have hi : p'.1.1 = p.1.1 := Sum.inl.inj (congrArg baseType h0)
    have hj : p'.1.2 = p.1.2 := Sum.inl.inj (congrArg baseType h1)
    have hp : p' = p := Subtype.ext (Prod.ext hi hj)
    subst p'
    have hd : d' = d := by simpa using h0
    have he : e' = e := by simpa using h1
    simpa [hd, he] using hlabel
  generalize hx : (.inl ⟨p.1.1, d⟩ : BaseVertex C) = x at h
  generalize hy : (.inl ⟨p.1.2, e⟩ : BaseVertex C) = y at h
  rcases h.2 with h | h
  · cases h with
    | main p' d' e' he => exact forward p' d' e' hx.symm hy.symm he
    | left h' d' => cases hx
    | right h' e' => cases hx
    | third h' q' f' => cases hx
  · cases h with
    | main p' d' e' he =>
      have hi : p.1.1 = p'.1.2 := Sum.inl.inj (congrArg baseType hx)
      have hj : p.1.2 = p'.1.1 := Sum.inl.inj (congrArg baseType hy)
      have := p.property
      have := p'.property
      omega
    | left h' d' => cases hy
    | right h' e' => cases hy
    | third h' q' f' => cases hy

lemma base_helper_left_label (h : Helper t) (q : C.Label h.1.1)
    (d : C.Domain h.1.1.1.1)
    (ha : (baseGraph C).Adj (.inr ⟨h, q⟩) (.inl ⟨h.1.1.1.1, d⟩)) :
    q = C.leftLabel h.1.1 d := by
  generalize hx : (.inr ⟨h, q⟩ : BaseVertex C) = x at ha
  generalize hy : (.inl ⟨h.1.1.1.1, d⟩ : BaseVertex C) = y at ha
  rcases ha.2 with ha | ha
  · cases ha with
    | main p' d' e' he => cases hx
    | left h' d' =>
      have hh : h = h' := Sum.inr.inj (congrArg baseType hx)
      subst h'
      have hq : q = C.leftLabel h.1.1 d' := by simpa using hx
      have hd : d = d' := by simpa using hy
      simpa [hd] using hq
    | right h' e' =>
      have hh : h = h' := Sum.inr.inj (congrArg baseType hx)
      subst h'
      have hi : h.1.1.1.1 = h.1.1.1.2 := Sum.inl.inj (congrArg baseType hy)
      exact ((ne_of_lt h.1.1.2) hi).elim
    | third h' q' f' =>
      have hh : h = h' := Sum.inr.inj (congrArg baseType hx)
      subst h'
      have hi : h.1.1.1.1 = h.1.2 := Sum.inl.inj (congrArg baseType hy)
      exact (h.2.1 hi.symm).elim
  · cases ha with
    | main p' d' e' he => cases hx
    | left h' d' => cases hx
    | right h' e' => cases hx
    | third h' q' f' => cases hx

lemma base_helper_right_label (h : Helper t) (q : C.Label h.1.1)
    (d : C.Domain h.1.1.1.2)
    (ha : (baseGraph C).Adj (.inr ⟨h, q⟩) (.inl ⟨h.1.1.1.2, d⟩)) :
    q = C.rightLabel h.1.1 d := by
  generalize hx : (.inr ⟨h, q⟩ : BaseVertex C) = x at ha
  generalize hy : (.inl ⟨h.1.1.1.2, d⟩ : BaseVertex C) = y at ha
  rcases ha.2 with ha | ha
  · cases ha with
    | main p' d' e' he => cases hx
    | right h' d' =>
      have hh : h = h' := Sum.inr.inj (congrArg baseType hx)
      subst h'
      have hq : q = C.rightLabel h.1.1 d' := by simpa using hx
      have hd : d = d' := by simpa using hy
      simpa [hd] using hq
    | left h' e' =>
      have hh : h = h' := Sum.inr.inj (congrArg baseType hx)
      subst h'
      have hi : h.1.1.1.2 = h.1.1.1.1 := Sum.inl.inj (congrArg baseType hy)
      exact ((ne_of_lt h.1.1.2) hi.symm).elim
    | third h' q' f' =>
      have hh : h = h' := Sum.inr.inj (congrArg baseType hx)
      subst h'
      have hi : h.1.1.1.2 = h.1.2 := Sum.inl.inj (congrArg baseType hy)
      exact (h.2.2 hi.symm).elim
  · cases ha with
    | main p' d' e' he => cases hx
    | left h' d' => cases hx
    | right h' e' => cases hx
    | third h' q' f' => cases hx

noncomputable def leftLabelAt (p : MainPair t) : BaseVertex C → Option (C.Label p)
  | .inl ⟨i, d⟩ => if h : i = p.1.1 then some (C.leftLabel p (h ▸ d)) else none
  | .inr _ => none

noncomputable def rightLabelAt (p : MainPair t) : BaseVertex C → Option (C.Label p)
  | .inl ⟨i, d⟩ => if h : i = p.1.2 then some (C.rightLabel p (h ▸ d)) else none
  | .inr _ => none

noncomputable def helperLabelAt (h : Helper t) : BaseVertex C → Option (C.Label h.1.1)
  | .inl _ => none
  | .inr ⟨j, q⟩ => if he : j = h then some (he ▸ q) else none

@[simp] lemma leftLabelAt_self (p : MainPair t) (d : C.Domain p.1.1) :
    leftLabelAt C p (.inl ⟨p.1.1, d⟩) = some (C.leftLabel p d) := by
  simp [leftLabelAt]

@[simp] lemma rightLabelAt_self (p : MainPair t) (d : C.Domain p.1.2) :
    rightLabelAt C p (.inl ⟨p.1.2, d⟩) = some (C.rightLabel p d) := by
  simp [rightLabelAt]

@[simp] lemma helperLabelAt_self (h : Helper t) (q : C.Label h.1.1) :
    helperLabelAt C h (.inr ⟨h, q⟩) = some q := by
  simp [helperLabelAt]

lemma base_main_labels {x y : BaseVertex C} (p : MainPair t)
    (hxy : (baseGraph C).Adj x y) (hx : baseType x = .inl p.1.1)
    (hy : baseType y = .inl p.1.2) : leftLabelAt C p x = rightLabelAt C p y := by
  obtain ⟨d, rfl⟩ := (baseType_inl_iff C x p.1.1).mp hx
  obtain ⟨e, rfl⟩ := (baseType_inl_iff C y p.1.2).mp hy
  simp [base_main_label C p d e hxy]

lemma base_helper_left_labels {x y : BaseVertex C} (h : Helper t)
    (hxy : (baseGraph C).Adj x y) (hx : baseType x = .inr h)
    (hy : baseType y = .inl h.1.1.1.1) :
    helperLabelAt C h x = leftLabelAt C h.1.1 y := by
  obtain ⟨q, rfl⟩ := (baseType_inr_iff C x h).mp hx
  obtain ⟨d, rfl⟩ := (baseType_inl_iff C y h.1.1.1.1).mp hy
  simp [base_helper_left_label C h q d hxy]

lemma base_helper_right_labels {x y : BaseVertex C} (h : Helper t)
    (hxy : (baseGraph C).Adj x y) (hx : baseType x = .inr h)
    (hy : baseType y = .inl h.1.1.1.2) :
    helperLabelAt C h x = rightLabelAt C h.1.1 y := by
  obtain ⟨q, rfl⟩ := (baseType_inr_iff C x h).mp hx
  obtain ⟨d, rfl⟩ := (baseType_inl_iff C y h.1.1.1.2).mp hy
  simp [base_helper_right_label C h q d hxy]

end BaseLabels

end ParityWL

end OAI
