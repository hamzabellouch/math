import OAI.Combinatorics.MatrixRemoval.Host
import OAI.Combinatorics.MatrixRemoval.DirectNonshattering

namespace OAI

/-!
# Nonshattering for the concrete canonical host

This is a direct application of the qualitative five-column obstruction to
`Problem348.Construction.host`. It needs no axis order and no injectivity
assumption on the five selected non-anchor columns.
-/

universe uR

namespace Problem348.Construction

open Finset

noncomputable section

/-- The two kinds of non-anchor positions, without their outer sum tag. -/
abbrev NonanchorPosition (h : ℕ) := VariablePosition h ⊕ Fin (2 ^ h)

/-- Column-class labels for the non-anchor induced submatrix. The dummy label
is irrelevant because dummy columns are treated separately. -/
def nonanchorClass {h : ℕ} : NonanchorPosition h → ℕ
  | Sum.inl v => v.1.val
  | Sum.inr _ => 0

def nonanchorKey {h : ℕ} : NonanchorPosition h → ℕ
  | Sum.inl v => node v
  | Sum.inr _ => 0

def nonanchorDummy {h : ℕ} : NonanchorPosition h → Prop
  | Sum.inl _ => False
  | Sum.inr _ => True

instance {h : ℕ} (x : NonanchorPosition h) : Decidable (nonanchorDummy x) := by
  cases x <;> simp only [nonanchorDummy] <;> infer_instance

/-- The three class labels that can contain ones in a variable row. -/
def variableSupportLabels {h : ℕ} (r : VariablePosition h) : Finset ℕ :=
  {r.1.val, 2 * (depth r - 1), 2 * (depth r - 1) + 1}

theorem variableSupportLabels_card_le {h : ℕ} (r : VariablePosition h) :
    (variableSupportLabels r).card ≤ 3 := by
  exact Finset.card_le_three

/-- The constant-class suffix property, stated for the actual host kernel. -/
theorem variableEntry_mono_class {h : ℕ} (r c d : VariablePosition h)
    (hclass : c.1.val = d.1.val) (hnode : node c ≤ node d)
    (hc : variableEntry r c = true) : variableEntry r d = true := by
  have hd : depth c = depth d := by simp only [depth, hclass]
  have hp : plus c = plus d := by simp only [plus, hclass]
  unfold variableEntry at hc ⊢
  simp only [hd, hp] at hc
  split_ifs at hc ⊢ <;> simp_all <;> omega

/-- A true variable entry has one of the three possible column-class labels. -/
theorem variableEntry_mem_support {h : ℕ} (r c : VariablePosition h)
    (hc : variableEntry r c = true) : c.1.val ∈ variableSupportLabels r := by
  have hr := r.1.isLt
  have hcv := c.1.isLt
  simp only [variableSupportLabels, Finset.mem_insert, Finset.mem_singleton]
  unfold variableEntry at hc
  simp only [depth, plus, decide_eq_true_eq] at hc ⊢
  split_ifs at hc <;> simp_all <;> omega

/-- The induced matrix on all non-anchor positions misses a five-bit word. -/
theorem nonanchor_host_not_surjective (h : ℕ)
    (selected : Fin 5 → NonanchorPosition h) :
    ¬ Function.Surjective
      (fun r : NonanchorPosition h =>
        fun i => host (Sum.inr r) (Sum.inr (selected i))) := by
  apply DirectNonshattering.not_surjective_selected_columns
    (fun r c : NonanchorPosition h => host (Sum.inr r) (Sum.inr c))
    nonanchorDummy nonanchorDummy nonanchorClass nonanchorKey
  · intro r hr c
    cases r with
    | inl r => exact False.elim hr
    | inr r => cases c <;> rfl
  · intro c hc r
    cases c with
    | inl c => exact False.elim hc
    | inr c => cases r <;> rfl
  · intro r hr c d hc hd hclass hnode he
    cases r with
    | inr r => exact False.elim (hr trivial)
    | inl r =>
      cases c with
      | inr c => exact False.elim (hc trivial)
      | inl c =>
        cases d with
        | inr d => exact False.elim (hd trivial)
        | inl d => exact variableEntry_mono_class r c d hclass hnode he
  · intro r hr
    cases r with
    | inr r => exact False.elim (hr trivial)
    | inl r =>
      apply (Finset.card_le_card ?_).trans (variableSupportLabels_card_le r)
      intro a ha
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨_, hnd, he⟩ := Finset.mem_filter.mp hc
      cases c with
      | inr c => exact False.elim (hnd trivial)
      | inl c => exact variableEntry_mem_support r c he

/-- The actual host, stated using its outer position type. This avoids any
choice of a separate non-anchor enumeration in anchor-rigidity applications. -/
theorem host_nonanchor_missing_word {h : ℕ} (columns : Fin 5 → Position h)
    (hcolumns : ∀ i, ∃ c : NonanchorPosition h, columns i = Sum.inr c) :
    ∃ w : Fin 5 → Bool, ∀ r : Position h,
      (∃ a : NonanchorPosition h, r = Sum.inr a) →
      (fun i => host r (columns i)) ≠ w := by
  classical
  choose selected hselected using hcolumns
  obtain ⟨w, hw⟩ : ∃ w : Fin 5 → Bool, ∀ r : NonanchorPosition h,
      (fun i => host (Sum.inr r) (Sum.inr (selected i))) ≠ w := by
    simpa only [Function.Surjective, not_forall, not_exists] using
      nonanchor_host_not_surjective h selected
  refine ⟨w, ?_⟩
  rintro r ⟨a, rfl⟩
  simpa only [hselected] using hw a

/-- Restricting to any collection of non-anchor rows still misses a word.
This is the form used for the final 32 rows of an alleged anchor copy. -/
theorem host_nonanchor_submatrix_not_surjective {h : ℕ} {R : Type uR}
    (rows : R → Position h) (columns : Fin 5 → Position h)
    (hrows : ∀ r, ∃ a : NonanchorPosition h, rows r = Sum.inr a)
    (hcolumns : ∀ i, ∃ c : NonanchorPosition h, columns i = Sum.inr c) :
    ¬ Function.Surjective (fun r i => host (rows r) (columns i)) := by
  obtain ⟨w, hw⟩ := host_nonanchor_missing_word columns hcolumns
  intro hsurj
  obtain ⟨r, hr⟩ := hsurj w
  exact hw (rows r) (hrows r) hr

/-- The outer sum tag gives a convenient intrinsic non-anchor predicate. -/
@[simp] theorem exists_nonanchor_iff_not_isLeft {h : ℕ} (x : Position h) :
    (∃ a : NonanchorPosition h, x = Sum.inr a) ↔ ¬ x.isLeft := by
  cases x <;> simp

/-- Pointwise missing-word property for concrete anchor rigidity. -/
theorem host_nonanchor_missing_entry {h : ℕ} (columns : Fin 5 → Position h)
    (hcolumns : ∀ i, ¬ (columns i).isLeft) :
    ∃ w : Fin 5 → Bool, ∀ r : Position h, ¬ r.isLeft →
      ∃ i, host r (columns i) ≠ w i := by
  obtain ⟨w, hw⟩ := host_nonanchor_missing_word columns
    (fun i => (exists_nonanchor_iff_not_isLeft (columns i)).mpr (hcolumns i))
  refine ⟨w, ?_⟩
  intro r hr
  have hne := hw r ((exists_nonanchor_iff_not_isLeft r).mpr hr)
  exact not_forall.mp (fun he => hne (funext he))

/-- The subtype formulation also avoids making any non-anchor choices. -/
theorem host_nonanchor_subtype_not_surjective {h : ℕ}
    (columns : Fin 5 → Position h) (hcolumns : ∀ i, ¬ (columns i).isLeft) :
    ¬ Function.Surjective
      (fun r : {x : Position h // ¬ x.isLeft} => fun i => host r.val (columns i)) := by
  apply host_nonanchor_submatrix_not_surjective
    (fun r : {x : Position h // ¬ x.isLeft} => r.val) columns
  · intro r
    exact (exists_nonanchor_iff_not_isLeft r.val).mpr r.property
  · intro i
    exact (exists_nonanchor_iff_not_isLeft (columns i)).mpr (hcolumns i)

end
end Problem348.Construction

end OAI
