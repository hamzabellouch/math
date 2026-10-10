import Mathlib

namespace OAI

/-!
A direct qualitative proof of the non-anchor trace obstruction.
No enumeration of suffix generators is needed.

If all binary words occur, any two selected columns in the same class can be
separated by a singleton word, contradicting their suffix monotonicity.
Thus all five classes are distinct. The word 11110 then uses four classes,
while a variable row uses at most three and a dummy row is all ones.
-/

universe uR uC uK uL uRho uBeta

namespace Problem348.DirectNonshattering

open Finset

/-- A surjective family of class-monotone words separates the column classes. -/
theorem class_injective_of_surjective
    {R : Type uR} {C : Type uC} {K : Type uK} [DecidableEq C] [LinearOrder K]
    {L : Type uL} (classOf : C → L) (key : C → K) (A : R → C → Bool)
    (hmono : ∀ r i j, classOf i = classOf j → key i ≤ key j →
      A r i = true → A r j = true)
    (hsurj : Function.Surjective A) : Function.Injective classOf := by
  intro i j hij
  by_contra hne
  rcases le_total (key i) (key j) with hle | hle
  · obtain ⟨r, hr⟩ := hsurj (fun x => decide (x = i))
    have hi : A r i = true := by rw [hr]; simp
    have hj : A r j = true := hmono r i j hij hle hi
    rw [hr] at hj
    simp [Ne.symm hne] at hj
  · obtain ⟨r, hr⟩ := hsurj (fun x => decide (x = j))
    have hj : A r j = true := by rw [hr]; simp
    have hi : A r i = true := hmono r j i hij.symm hle hj
    rw [hr] at hi
    simp [hne] at hi

/-- General form: `q + 2` columns cannot be shattered by classwise suffix
rows supported on at most `q` classes, together with all-one rows. -/
theorem not_surjective_of_card
    {R : Type uR} {C : Type uC} {L : Type uL} {K : Type uK} [Fintype C] [DecidableEq C] [DecidableEq L]
    [LinearOrder K] (q : ℕ) (hcard : q + 2 ≤ Fintype.card C)
    (classOf : C → L) (key : C → K) (A : R → C → Bool)
    (hmono : ∀ r i j, classOf i = classOf j → key i ≤ key j →
      A r i = true → A r j = true)
    (hsupport : ∀ r,
      ((univ.filter (fun i => A r i = true)).image classOf).card ≤ q ∨
      (∀ i, A r i = true)) :
    ¬ Function.Surjective A := by
  classical
  intro hsurj
  have hinj := class_injective_of_surjective classOf key A hmono hsurj
  have : Nonempty C := Fintype.card_pos_iff.mp (by omega)
  let j : C := Classical.arbitrary C
  obtain ⟨r, hr⟩ := hsurj (fun i => decide (i ≠ j))
  rcases hsupport r with hs | hd
  · rw [hr, card_image_of_injective _ hinj] at hs
    change (univ.filter (fun i : C => decide (i ≠ j) = true)).card ≤ q at hs
    have hfilter : (univ.filter (fun i : C => decide (i ≠ j) = true)) =
        univ.erase j := by
      ext i
      simp
    rw [hfilter, card_erase_of_mem (mem_univ j), card_univ] at hs
    omega
  · have hj := hd j
    rw [hr] at hj
    simp at hj

/-- No family with suffixes in at most three classes, plus all-one rows,
realizes every binary word on five columns. -/
theorem not_surjective_five
    {R : Type uR} {L : Type uL} {K : Type uK} [DecidableEq L] [LinearOrder K]
    (classOf : Fin 5 → L) (key : Fin 5 → K) (A : R → Fin 5 → Bool)
    (hmono : ∀ r i j, classOf i = classOf j → key i ≤ key j →
      A r i = true → A r j = true)
    (hsupport : ∀ r,
      ((univ.filter (fun i => A r i = true)).image classOf).card ≤ 3 ∨
      (∀ i, A r i = true)) :
    ¬ Function.Surjective A :=
  not_surjective_of_card 3 (by simp) classOf key A hmono hsupport

/-- The conclusion in a form convenient for a five-column shattering test. -/
theorem exists_missing_word
    {R : Type uR} {L : Type uL} {K : Type uK} [DecidableEq L] [LinearOrder K]
    (classOf : Fin 5 → L) (key : Fin 5 → K) (A : R → Fin 5 → Bool)
    (hmono : ∀ r i j, classOf i = classOf j → key i ≤ key j →
      A r i = true → A r j = true)
    (hsupport : ∀ r,
      ((univ.filter (fun i => A r i = true)).image classOf).card ≤ 3 ∨
      (∀ i, A r i = true)) :
    ∃ w : Fin 5 → Bool, ∀ r, A r ≠ w := by
  simpa only [Function.Surjective, not_forall, not_exists] using
    not_surjective_five classOf key A hmono hsupport

/-- A column equal to one in every row also rules out shattering immediately. -/
theorem not_surjective_of_constant_column
    {R : Type uR} {C : Type uC} (A : R → C → Bool) (j : C)
    (hj : ∀ r, A r j = true) : ¬ Function.Surjective A := by
  intro hsurj
  obtain ⟨r, hr⟩ := hsurj (fun _ => false)
  have h := hj r
  rw [hr] at h
  cases h

/-- Whole-host version.  Dummy columns are all ones, and every non-dummy row
has at most three active classes among the non-dummy columns.  The chosen five
columns need not be ordered or even assumed distinct. -/
theorem not_surjective_selected_columns
    {R : Type uR} {C : Type uC} {L : Type uL} {K : Type uK} [Fintype C] [DecidableEq C] [DecidableEq L]
    [LinearOrder K]
    (A : R → C → Bool) (dummyRow : R → Prop) (dummyColumn : C → Prop)
    [DecidablePred dummyColumn]
    (classOf : C → L) (key : C → K)
    (hrow : ∀ r, dummyRow r → ∀ c, A r c = true)
    (hcolumn : ∀ c, dummyColumn c → ∀ r, A r c = true)
    (hmono : ∀ r, ¬ dummyRow r → ∀ c d,
      ¬ dummyColumn c → ¬ dummyColumn d → classOf c = classOf d →
      key c ≤ key d → A r c = true → A r d = true)
    (hsupport : ∀ r, ¬ dummyRow r →
      ((univ.filter (fun c => ¬ dummyColumn c ∧ A r c = true)).image classOf).card ≤ 3)
    (selected : Fin 5 → C) :
    ¬ Function.Surjective (fun r i => A r (selected i)) := by
  classical
  by_cases hdummy : ∃ i, dummyColumn (selected i)
  · obtain ⟨i, hi⟩ := hdummy
    exact not_surjective_of_constant_column (fun r j => A r (selected j)) i
      (hcolumn (selected i) hi)
  · have hnondummy : ∀ i, ¬ dummyColumn (selected i) := by
      simpa only [not_exists] using hdummy
    apply not_surjective_five (classOf ∘ selected) (key ∘ selected)
      (fun r i => A r (selected i))
    · intro r i j hij hle hi
      by_cases hr : dummyRow r
      · exact hrow r hr (selected j)
      · exact hmono r hr (selected i) (selected j)
          (hnondummy i) (hnondummy j) hij hle hi
    · intro r
      by_cases hr : dummyRow r
      · exact Or.inr (fun i => hrow r hr (selected i))
      · left
        refine (card_le_card (show
          (univ.filter (fun i => A r (selected i) = true)).image (classOf ∘ selected) ⊆
          (univ.filter (fun c => ¬ dummyColumn c ∧ A r c = true)).image classOf
          from ?_)).trans (hsupport r hr)
        intro l hl
        obtain ⟨i, hi, rfl⟩ := mem_image.mp hl
        exact mem_image.mpr ⟨selected i,
          mem_filter.mpr ⟨mem_univ _, hnondummy i, (mem_filter.mp hi).2⟩, rfl⟩


/-- On `k+2` coordinates, classwise monotone traces with at most `k`
active classes, allowing also the constant-one trace, omit a Boolean word.
The rank need not be injective within a class. -/
theorem exists_missing_word_with_zero {ρ : Type uRho} {β : Type uBeta} [DecidableEq β] (k : ℕ)
    (cls : Fin (k + 2) → β) (key : Fin (k + 2) → ℕ)
    (trace : ρ → Fin (k + 2) → Bool)
    (hup : ∀ r a b, cls a = cls b → key a ≤ key b →
      trace r a = true → trace r b = true)
    (hsupport : ∀ r, (∀ j, trace r j = true) ∨
      ((Finset.univ.filter (fun j => trace r j = true)).image cls).card ≤ k) :
    ∃ word : Fin (k + 2) → Bool,
      (∃ j, word j = false) ∧ ∀ r, trace r ≠ word := by
  classical
  by_cases hinj : Function.Injective cls
  · let word : Fin (k + 2) → Bool := fun j => decide (j ≠ 0)
    refine ⟨word, ⟨0, by simp [word]⟩, ?_⟩
    intro r heq
    rcases hsupport r with hall | hsmall
    · have hzero := hall 0
      rw [heq] at hzero
      simp [word] at hzero
    · rw [heq] at hsmall
      rw [Finset.card_image_of_injective _ hinj] at hsmall
      have hset : Finset.univ.filter (fun j : Fin (k + 2) => word j = true) =
          Finset.univ.erase 0 := by
        ext j
        simp [word]
      rw [hset] at hsmall
      simp at hsmall
  · obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp hinj
    have hp : ∃ a b : Fin (k + 2),
        a ≠ b ∧ cls a = cls b ∧ key a ≤ key b := by
      rcases le_total (key a) (key b) with h | h
      · exact ⟨a, b, hne, hab, h⟩
      · exact ⟨b, a, hne.symm, hab.symm, h⟩
    obtain ⟨a, b, hne, hab, hkey⟩ := hp
    let word : Fin (k + 2) → Bool := fun j => decide (j = a)
    refine ⟨word, ⟨b, by simp [word, hne.symm]⟩, ?_⟩
    intro r heq
    have ha : trace r a = true := by simp [heq, word]
    have hb := hup r a b hab hkey ha
    simp [heq, word, hne.symm] at hb

/-- Coordinatewise form of the missing-word theorem. -/
theorem exists_missing_word_pointwise {ρ : Type uRho} {β : Type uBeta} [DecidableEq β] (k : ℕ)
    (cls : Fin (k + 2) → β) (key : Fin (k + 2) → ℕ)
    (trace : ρ → Fin (k + 2) → Bool)
    (hup : ∀ r a b, cls a = cls b → key a ≤ key b →
      trace r a = true → trace r b = true)
    (hsupport : ∀ r, (∀ j, trace r j = true) ∨
      ((Finset.univ.filter (fun j => trace r j = true)).image cls).card ≤ k) :
    ∃ word : Fin (k + 2) → Bool, ∀ r, ∃ j, trace r j ≠ word j := by
  classical
  obtain ⟨word, _, hw⟩ := exists_missing_word_with_zero k cls key trace hup hsupport
  refine ⟨word, fun r => ?_⟩
  by_contra h
  push Not at h
  exact hw r (funext h)

/-- Matrix-facing form, handling both dummy columns and dummy rows.
No injectivity assumption on the selected columns is needed. -/
theorem matrix_missing_word {R : Type uR} {C : Type uC} {β : Type uBeta} [DecidableEq β] (k : ℕ)
    (A : R → C → Bool) (cols : Fin (k + 2) → C)
    (cls : C → β) (key : C → ℕ) (dummyRow : R → Prop) (dummyCol : C → Prop)
    (hdummyRow : ∀ r, dummyRow r → ∀ c, A r c = true)
    (hdummyCol : ∀ c, dummyCol c → ∀ r, A r c = true)
    (hup : ∀ r, ¬ dummyRow r → ∀ a b,
      ¬ dummyCol a → ¬ dummyCol b → cls a = cls b → key a ≤ key b →
      A r a = true → A r b = true)
    (hsupport : ∀ r, ¬ dummyRow r →
      (∀ j, ¬ dummyCol (cols j)) →
      ((Finset.univ.filter (fun j => A r (cols j) = true)).image
        (cls ∘ cols)).card ≤ k) :
    ∃ word : Fin (k + 2) → Bool, ∀ r, ∃ j, A r (cols j) ≠ word j := by
  classical
  by_cases hd : ∃ j, dummyCol (cols j)
  · obtain ⟨j, hj⟩ := hd
    refine ⟨fun _ => false, fun r => ⟨j, ?_⟩⟩
    simp [hdummyCol (cols j) hj r]
  · push Not at hd
    apply exists_missing_word_pointwise k (cls ∘ cols) (key ∘ cols)
      (fun r j => A r (cols j))
    · intro r a b hab hkey ha
      by_cases hr : dummyRow r
      · exact hdummyRow r hr (cols b)
      · exact hup r hr (cols a) (cols b) (hd a) (hd b) hab hkey ha
    · intro r
      by_cases hr : dummyRow r
      · exact Or.inl (fun j => hdummyRow r hr (cols j))
      · exact Or.inr (hsupport r hr hd)

/-- An explicit cover by at most `k` column classes is enough for the
support premise. This form avoids cardinal computations on selected columns. -/
theorem matrix_missing_word_of_class_cover {R : Type uR} {C : Type uC} {β : Type uBeta} [DecidableEq β] (k : ℕ)
    (A : R → C → Bool) (cols : Fin (k + 2) → C)
    (cls : C → β) (key : C → ℕ) (dummyRow : R → Prop) (dummyCol : C → Prop)
    (hdummyRow : ∀ r, dummyRow r → ∀ c, A r c = true)
    (hdummyCol : ∀ c, dummyCol c → ∀ r, A r c = true)
    (hup : ∀ r, ¬ dummyRow r → ∀ a b,
      ¬ dummyCol a → ¬ dummyCol b → cls a = cls b → key a ≤ key b →
      A r a = true → A r b = true)
    (hcover : ∀ r, ¬ dummyRow r → ∃ S : Finset β, S.card ≤ k ∧
      ∀ c, ¬ dummyCol c → A r c = true → cls c ∈ S) :
    ∃ word : Fin (k + 2) → Bool, ∀ r, ∃ j, A r (cols j) ≠ word j := by
  classical
  apply matrix_missing_word k A cols cls key dummyRow dummyCol hdummyRow hdummyCol hup
  intro r hr hcols
  obtain ⟨S, hS, hmem⟩ := hcover r hr
  apply le_trans (Finset.card_le_card ?_) hS
  intro c hc
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hc
  exact hmem (cols j) (hcols j) (Finset.mem_filter.mp hj).2

end Problem348.DirectNonshattering

end OAI
