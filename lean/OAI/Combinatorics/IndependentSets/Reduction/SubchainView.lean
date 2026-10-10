import Mathlib
import OAI.Combinatorics.IndependentSets.Reduction.OccurrenceTuple

namespace OAI

namespace LargeIndependentSets
open scoped Classical BigOperators

@[ext] structure SubchainView (U V L R : Type*) (n : ℕ) (I : Finset (Fin (n+1))) where
  question : ∀ j : I, MixedTuple U V n j.val.val
  projection : ∀ i j : I, i.val ≤ j.val →
    MixedTuple L R n i.val.val → MixedTuple L R n j.val.val

def chainView {U V L R C : Type*} (lc : LabelCoverData U V L R C)
    {n : ℕ} (c : Fin n → C) (I : Finset (Fin (n+1))) : SubchainView U V L R n I where
  question j := occurrenceTuple lc c j.val.val
  projection i j hij := chainComposite lc c i.val.val j.val.val hij

lemma occurrenceTuple_local_left {U V L R C : Type*} (lc : LabelCoverData U V L R C)
    {n : ℕ} {c c' : Fin n → C} (h : Fin n)
    (hout : ∀ k, k ≠ h → c k = c' k) (hown : lc.left (c h) = lc.left (c' h))
    {i : ℕ} (hi : i ≤ h.val) : occurrenceTuple lc c i = occurrenceTuple lc c' i := by
  apply Subtype.ext; funext k
  by_cases hk : k = h
  · subst k; simp [occurrenceTuple, show ¬ h.val < i by omega, hown]
  · simp [occurrenceTuple, hout k hk]

lemma occurrenceTuple_local_right {U V L R C : Type*} (lc : LabelCoverData U V L R C)
    {n : ℕ} {c c' : Fin n → C} (h : Fin n)
    (hout : ∀ k, k ≠ h → c k = c' k) (hown : lc.right (c h) = lc.right (c' h))
    {i : ℕ} (hi : h.val < i) : occurrenceTuple lc c i = occurrenceTuple lc c' i := by
  apply Subtype.ext; funext k
  by_cases hk : k = h
  · subst k; simp [occurrenceTuple, hi, hown]
  · simp [occurrenceTuple, hout k hk]

lemma chainComposite_local {U V L R C : Type*} (lc : LabelCoverData U V L R C)
    {n : ℕ} {c c' : Fin n → C} (h : Fin n)
    (hout : ∀ k, k ≠ h → c k = c' k) {i j : ℕ} (hij : i ≤ j)
    (haway : j ≤ h.val ∨ h.val < i) :
    chainComposite lc c i j hij = chainComposite lc c' i j hij := by
  funext x; apply Subtype.ext; funext k
  by_cases hk : k = h
  · subst k
    have hh : ¬(i ≤ h.val ∧ h.val < j) := by omega
    simp [chainComposite, hh]
  · simp [chainComposite, hout k hk]

lemma chainView_local_left {U V L R C : Type*} (lc : LabelCoverData U V L R C)
    {n : ℕ} {c c' : Fin n → C} (h : Fin n)
    (hout : ∀ k, k ≠ h → c k = c' k) (hown : lc.left (c h) = lc.left (c' h))
    (I : Finset (Fin (n+1))) (hI : ∀ i ∈ I, i.val ≤ h.val) :
    chainView lc c I = chainView lc c' I := by
  apply SubchainView.ext
  · funext i; exact occurrenceTuple_local_left lc h hout hown (hI i.val i.property)
  · funext i j hij
    exact chainComposite_local lc h hout hij (Or.inl (hI j.val j.property))

lemma chainView_local_right {U V L R C : Type*} (lc : LabelCoverData U V L R C)
    {n : ℕ} {c c' : Fin n → C} (h : Fin n)
    (hout : ∀ k, k ≠ h → c k = c' k) (hown : lc.right (c h) = lc.right (c' h))
    (I : Finset (Fin (n+1))) (hI : ∀ i ∈ I, h.val < i.val) :
    chainView lc c I = chainView lc c' I := by
  apply SubchainView.ext
  · funext i; exact occurrenceTuple_local_right lc h hout hown (hI i.val i.property)
  · funext i j hij
    exact chainComposite_local lc h hout hij (Or.inr (hI i.val i.property))

abbrev SubchainCoord (L R : Type*) (n : ℕ) (I : Finset (Fin (n+1))) :=
  Σ j : I, MixedTuple L R n j.val.val

noncomputable def leftEntry {L R : Type*} [Nonempty L] {n i : ℕ}
    (h : Fin n) (x : MixedTuple L R n i) : L := (x.val h).elim (fun _ => Classical.arbitrary L) id
noncomputable def rightEntry {L R : Type*} [Nonempty R] {n i : ℕ}
    (h : Fin n) (x : MixedTuple L R n i) : R := (x.val h).elim id (fun _ => Classical.arbitrary R)

lemma leftEntry_spec {L R : Type*} [Nonempty L] {n i : ℕ}
    (h : Fin n) (x : MixedTuple L R n i) (hi : i ≤ h.val) :
    x.val h = Sum.inr (leftEntry h x) := by
  have hp := x.property h
  simp only [show ¬h.val < i by omega, decide_false] at hp
  unfold leftEntry
  cases he : x.val h <;> simp_all

lemma rightEntry_spec {L R : Type*} [Nonempty R] {n i : ℕ}
    (h : Fin n) (x : MixedTuple L R n i) (hi : h.val < i) :
    x.val h = Sum.inl (rightEntry h x) := by
  have hp := x.property h
  simp only [hi, decide_true] at hp
  unfold rightEntry
  cases he : x.val h <;> simp_all

noncomputable def terminalList {U V L R C : Type*} (lc : LabelCoverData U V L R C)
    {n : ℕ} (c : Fin n → C) (I : Finset (Fin (n+1)))
    (S : Finset (SubchainCoord L R n I)) : Finset (MixedTuple L R n n) :=
  S.image (fun x => chainComposite lc c x.1.val.val n (by have := x.1.val.isLt; omega) x.2)

lemma terminal_intersection_decodes {U V L R C : Type*} [Nonempty L] [Nonempty R]
    (lc : LabelCoverData U V L R C) {n : ℕ} (c : Fin n → C) (h : Fin n)
    (I J : Finset (Fin (n+1))) (hI : ∀ i ∈ I, i.val ≤ h.val)
    (hJ : ∀ j ∈ J, h.val < j.val)
    (S : Finset (SubchainCoord L R n I)) (S' : Finset (SubchainCoord L R n J))
    (hinter : ¬ Disjoint (terminalList lc c I S) (terminalList lc c J S')) :
    ∃ l ∈ S.image (fun x => leftEntry h x.2),
      ∃ r ∈ S'.image (fun x => rightEntry h x.2), lc.project (c h) l = r := by
  obtain ⟨z,hz,hz'⟩ := Finset.not_disjoint_iff.mp hinter
  obtain ⟨x,hx,he⟩ := Finset.mem_image.mp hz
  obtain ⟨y,hy,he'⟩ := Finset.mem_image.mp hz'
  refine ⟨leftEntry h x.2, Finset.mem_image.mpr ⟨x,hx,rfl⟩,
    rightEntry h y.2, Finset.mem_image.mpr ⟨y,hy,rfl⟩,?_⟩
  have hp := congrArg (fun z : MixedTuple L R n n => z.val h) (he.trans he'.symm)
  have hix := hI x.1.val x.1.property
  have hjy := hJ y.1.val y.1.property
  simp only [chainComposite, hix, h.isLt, and_self, ite_true,
    show ¬ y.1.val.val ≤ h.val by omega, false_and, ite_false,
    leftEntry_spec h x.2 hix, rightEntry_spec h y.2 hjy, Sum.elim_inr] at hp
  exact Sum.inl.inj hp

noncomputable def ownQuestionList {C U X : Type*} (q : C → U) (f : C → Finset X)
    (u : U) : Finset X :=
  if h : ∃ c, q c = u then f h.choose else ∅

lemma ownQuestionList_apply {C U X : Type*} (q : C → U) (f : C → Finset X)
    (hf : ∀ c c', q c = q c' → f c = f c') (c : C) :
    ownQuestionList q f (q c) = f c := by
  simp only [ownQuestionList, dite_eq_left (show ∃ c', q c' = q c from ⟨c,rfl⟩)]
  exact hf _ _ (Exists.choose_spec (show ∃ c', q c' = q c from ⟨c,rfl⟩))

lemma ownQuestionList_card {C U X : Type*} (q : C → U) (f : C → Finset X)
    {d : ℕ} (hf : ∀ c, (f c).card ≤ d) (u : U) :
    (ownQuestionList q f u).card ≤ d := by
  unfold ownQuestionList; split_ifs <;> simp_all

theorem separated_lists_conditioned {U V L R C : Type*}
    [Fintype C] [Nonempty L] [Nonempty R]
    (lc : LabelCoverData U V L R C) {σ : ℝ} (hsound : lc.Sound σ)
    {n : ℕ} (background : Fin n → C) (h : Fin n)
    (I J : Finset (Fin (n+1))) (hI : ∀ i ∈ I, i.val ≤ h.val)
    (hJ : ∀ j ∈ J, h.val < j.val) (d : ℕ)
    (ruleI : SubchainView U V L R n I → Finset (SubchainCoord L R n I))
    (ruleJ : SubchainView U V L R n J → Finset (SubchainCoord L R n J))
    (hcardI : ∀ v, (ruleI v).card ≤ d) (hcardJ : ∀ v, (ruleJ v).card ≤ d) :
    ((Finset.univ.filter (fun c : C =>
      let chain := Function.update background h c
      ¬ Disjoint (terminalList lc chain I (ruleI (chainView lc chain I)))
        (terminalList lc chain J (ruleJ (chainView lc chain J))))).card : ℝ) ≤
      (d : ℝ)^2 * σ * Fintype.card C := by
  let chain := fun c => Function.update background h c
  let lefts := fun c => (ruleI (chainView lc (chain c) I)).image (fun x => leftEntry h x.2)
  let rights := fun c => (ruleJ (chainView lc (chain c) J)).image (fun x => rightEntry h x.2)
  have hout (c c' : C) (k : Fin n) (hk : k ≠ h) : chain c k = chain c' k := by
    simp [chain, Function.update_of_ne hk]
  have hleft (c c' : C) (he : lc.left c = lc.left c') : lefts c = lefts c' := by
    have hv := chainView_local_left lc h (hout c c') (by simpa [chain] using he) I hI
    simp only [lefts, hv]
  have hright (c c' : C) (he : lc.right c = lc.right c') : rights c = rights c' := by
    have hv := chainView_local_right lc h (hout c c') (by simpa [chain] using he) J hJ
    simp only [rights, hv]
  let A := ownQuestionList lc.left lefts
  let B := ownQuestionList lc.right rights
  have hA (u) : (A u).card ≤ d :=
    ownQuestionList_card _ _ (fun c => Finset.card_image_le.trans (hcardI _)) u
  have hB (v) : (B v).card ≤ d :=
    ownQuestionList_card _ _ (fun c => Finset.card_image_le.trans (hcardJ _)) v
  have hcover : Finset.univ.filter (fun c : C =>
      ¬Disjoint (terminalList lc (chain c) I (ruleI (chainView lc (chain c) I)))
        (terminalList lc (chain c) J (ruleJ (chainView lc (chain c) J)))) ⊆
      Finset.univ.filter (fun c => ∃ l ∈ A (lc.left c), ∃ r ∈ B (lc.right c), lc.project c l = r) := by
    intro c hc
    have hd := terminal_intersection_decodes lc (chain c) h I J hI hJ _ _
      (Finset.mem_filter.mp hc).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    change ∃ l ∈ ownQuestionList lc.left lefts (lc.left c),
      ∃ r ∈ ownQuestionList lc.right rights (lc.right c), lc.project c l = r
    rw [ownQuestionList_apply _ _ hleft, ownQuestionList_apply _ _ hright]
    simpa only [chain, Function.update_self] using hd
  exact (show (_ : ℝ) ≤ _ from Nat.cast_le.mpr (Finset.card_le_card hcover)).trans
    (bounded_list_decoding lc hsound d A B hA hB)

end LargeIndependentSets

end OAI
