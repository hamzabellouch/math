import Mathlib.Logic.Equiv.Set
import OAI.Computability.PerfectCompleteness.Construction.LocalCompletionFamily

namespace OAI


namespace PerfectCompleteness.FlexibleLocalCompletion

open scoped Classical
open CompletionSoundness CompletionSoundness.LegalProjectionGame

noncomputable section

variable {E Q₁ Q₂ : Type*} [Fintype E]
  {L : Q₁ → Type*} {R : Q₂ → Type*} [∀ x, Fintype (L x)]
  {q : Nat}
  (G : LegalProjectionGame E Q₁ Q₂ L R)
  (legalL : ∀ x, L x ↪ Fin (2 * q)) (legalR : ∀ y, R y ↪ Fin q)

structure Compatible (data : E → LocalCompletionFamily.Input q) : Prop where
  mask : ∀ e a, (data e).1 a = true ↔ a ∈ Set.range (legalL (G.left e))
  image : ∀ e l, (data e).2 (legalL (G.left e) l) =
    legalR (G.right e) (G.projection e l)

variable (data : E → LocalCompletionFamily.Input q)
  (compatible : Compatible G legalL legalR data)

def localLegalEquiv (e : E) : L (G.left e) ≃ LocalCompletionFamily.Legal (data e) :=
  (Equiv.ofInjective (legalL (G.left e)) (legalL (G.left e)).injective).trans
    (Equiv.subtypeEquivRight (fun a => (compatible.mask e a).symm))

omit [∀ x, Fintype (L x)] in
@[simp] theorem localLegalEquiv_apply_val (e : E) (l : L (G.left e)) :
    (localLegalEquiv G legalL legalR data compatible e l).val = legalL (G.left e) l := rfl

include legalL legalR compatible in
theorem card_legal (e : E) :
    Fintype.card (LocalCompletionFamily.Legal (data e)) = Fintype.card (L (G.left e)) :=
  (Fintype.card_congr (localLegalEquiv G legalL legalR data compatible e)).symm

include legalL legalR compatible in

theorem input_admissible
    (hsmall : ∀ e b, Fintype.card {l : L (G.left e) // G.projection e l = b} ≤ 2)
    (e : E) : LocalCompletionFamily.Admissible (data e) := by
  intro b
  rw [Fintype.card_eq_nat_card]
  have hmatch (l : L (G.left e)) :
      (data e).2 (localLegalEquiv G legalL legalR data compatible e l).val =
        legalR (G.right e) (G.projection e l) := by
    rw [localLegalEquiv_apply_val]
    exact compatible.image e l
  let fibers : {l : L (G.left e) // legalR (G.right e) (G.projection e l) = b} ≃
      {a : LocalCompletionFamily.Legal (data e) // (data e).2 a.val = b} :=
    (localLegalEquiv G legalL legalR data compatible e).subtypeEquiv
      (fun l => by rw [hmatch l])
  have hcard := Nat.card_congr fibers
  have hbound := embedded_fiber_le_two (legalR (G.right e)) (G.projection e) (hsmall e) b
  rw [Fintype.card_eq_nat_card] at hbound
  exact hcard.symm.le.trans hbound

def result (hq : 0 < q) (e : E) : LocalCompletionFamily.Result q :=
  LocalCompletionFamily.lookup hq (data e)

include legalL legalR compatible in
theorem result_correct (hq : 0 < q)
    (hsmall : ∀ e b, Fintype.card {l : L (G.left e) // G.projection e l = b} ≤ 2)
    (e : E) : LocalCompletionFamily.Correct (data e) (result data hq e) :=
  LocalCompletionFamily.lookup_correct hq (data e)
    (input_admissible G legalL legalR data compatible hsmall e)

def family (hq : 0 < q)
    (hsmall : ∀ e b, Fintype.card {l : L (G.left e) // G.projection e l = b} ≤ 2) :
    G.CompletionFamily legalL legalR where
  size e := LocalCompletionFamily.activeCount (result data hq e)
  positive e := LocalCompletionFamily.activeCount_positive _
  map e := LocalCompletionFamily.table (result data hq e)
  agrees e seed l :=
    ((result_correct G legalL legalR data compatible hq hsmall e).agrees seed
      (legalL (G.left e) l) ((compatible.mask e _).2 ⟨l, rfl⟩)).trans
      (compatible.image e l)
  exact_two e seed b := by
    rw [Fintype.card_eq_nat_card]
    have h := (result_correct G legalL legalR data compatible hq hsmall e).exact_two seed b
    rw [Fintype.card_eq_nat_card] at h
    exact h
  illegal_probability e a b := by
    have hmask : (data e).1 a.val ≠ true := by
      intro h
      exact a.property ((compatible.mask e a.val).1 h)
    have h := (result_correct G legalL legalR data compatible hq hsmall e).illegal_probability
      a.val hmask b
    simpa only [Fintype.card_fin, card_legal G legalL legalR data compatible] using h

@[simp] theorem family_size (hq : 0 < q)
    (hsmall : ∀ e b, Fintype.card {l : L (G.left e) // G.projection e l = b} ≤ 2) (e : E) :
    (family G legalL legalR data compatible hq hsmall).size e =
      LocalCompletionFamily.activeCount (LocalCompletionFamily.lookup hq (data e)) := rfl

@[simp] theorem family_map (hq : 0 < q)
    (hsmall : ∀ e b, Fintype.card {l : L (G.left e) // G.projection e l = b} ≤ 2) (e : E) :
    (family G legalL legalR data compatible hq hsmall).map e =
      LocalCompletionFamily.table (LocalCompletionFamily.lookup hq (data e)) := rfl

theorem family_size_le (hq : 0 < q)
    (hsmall : ∀ e b, Fintype.card {l : L (G.left e) // G.projection e l = b} ≤ 2) (e : E) :
    (family G legalL legalR data compatible hq hsmall).size e ≤ 2 * q :=
  LocalCompletionFamily.activeCount_le (result data hq e)

end
end PerfectCompleteness.FlexibleLocalCompletion


namespace PerfectCompleteness.LocalCompletionGame

open scoped Classical
open UniqueGamesTheorem.Foundations.Games
open CompletionSoundness CompletionSoundness.LegalProjectionGame

noncomputable section

variable {E Q₁ Q₂ : Type*} [Fintype E]
  {L : Q₁ → Type*} {R : Q₂ → Type*} [∀ x, Fintype (L x)]
  {q : Nat}
  (G : LegalProjectionGame E Q₁ Q₂ L R)
  (legalL : ∀ x, L x ↪ Fin (2 * q)) (legalR : ∀ y, R y ↪ Fin q)
  (defaultL : ∀ x, L x)

def input (e : E) : LocalCompletionFamily.Input q :=
  (fun a => decide (a ∈ Set.range (legalL (G.left e))),
    fun a => legalR (G.right e)
      (G.projection e (roundLabel (legalL (G.left e)) (defaultL (G.left e)) a)))

theorem input_mask_true (e : E) (a : Fin (2 * q)) :
    (input G legalL legalR defaultL e).1 a = true ↔
      a ∈ Set.range (legalL (G.left e)) := by
  simp only [input, decide_eq_true_iff]

theorem input_image_legal (e : E) (l : L (G.left e)) :
    (input G legalL legalR defaultL e).2 (legalL (G.left e) l) =
      legalR (G.right e) (G.projection e l) := by
  simp only [input, roundLabel_legal]

def localLegalEquiv (e : E) :
    L (G.left e) ≃ LocalCompletionFamily.Legal (input G legalL legalR defaultL e) where
  toFun l := ⟨legalL (G.left e) l,
    (input_mask_true G legalL legalR defaultL e _).2 ⟨l, rfl⟩⟩
  invFun a := roundLabel (legalL (G.left e)) (defaultL (G.left e)) a.val
  left_inv l := roundLabel_legal (legalL (G.left e)) (defaultL (G.left e)) l
  right_inv a := by
    apply Subtype.ext
    obtain ⟨l, hl⟩ := (input_mask_true G legalL legalR defaultL e a.val).1 a.property
    change legalL (G.left e)
      (roundLabel (legalL (G.left e)) (defaultL (G.left e)) a.val) = a.val
    rw [← hl, roundLabel_legal]

@[simp] theorem localLegalEquiv_apply_val (e : E) (l : L (G.left e)) :
    (localLegalEquiv G legalL legalR defaultL e l).val = legalL (G.left e) l := rfl

theorem card_legal (e : E) :
    Fintype.card (LocalCompletionFamily.Legal (input G legalL legalR defaultL e)) =
      Fintype.card (L (G.left e)) :=
  (Fintype.card_congr (localLegalEquiv G legalL legalR defaultL e)).symm

theorem input_admissible
    (hsmall : ∀ e b, Fintype.card {l : L (G.left e) // G.projection e l = b} ≤ 2)
    (e : E) : LocalCompletionFamily.Admissible (input G legalL legalR defaultL e) := by
  intro b
  have hmatch (l : L (G.left e)) :
      (input G legalL legalR defaultL e).2
        (localLegalEquiv G legalL legalR defaultL e l).val =
        legalR (G.right e) (G.projection e l) := by
    rw [localLegalEquiv_apply_val]
    exact input_image_legal G legalL legalR defaultL e l
  let fibers : {l : L (G.left e) // legalR (G.right e) (G.projection e l) = b} ≃
      {a : LocalCompletionFamily.Legal (input G legalL legalR defaultL e) //
        (input G legalL legalR defaultL e).2 a.val = b} :=
    (localLegalEquiv G legalL legalR defaultL e).subtypeEquiv
      (fun l => by rw [hmatch l])
  have hcard := Fintype.card_congr fibers
  have hbound := embedded_fiber_le_two (legalR (G.right e)) (G.projection e) (hsmall e) b
  simp only [← Nat.card_eq_fintype_card] at hcard hbound ⊢
  exact hcard.symm.le.trans hbound

def result (hq : 0 < q) (e : E) : LocalCompletionFamily.Result q :=
  LocalCompletionFamily.lookup hq (input G legalL legalR defaultL e)

theorem result_correct (hq : 0 < q)
    (hsmall : ∀ e b, Fintype.card {l : L (G.left e) // G.projection e l = b} ≤ 2)
    (e : E) : LocalCompletionFamily.Correct (input G legalL legalR defaultL e)
      (result G legalL legalR defaultL hq e) :=
  LocalCompletionFamily.lookup_correct hq _
    (input_admissible G legalL legalR defaultL hsmall e)

def family (hq : 0 < q)
    (hsmall : ∀ e b, Fintype.card {l : L (G.left e) // G.projection e l = b} ≤ 2) :
    G.CompletionFamily legalL legalR where
  size e := LocalCompletionFamily.activeCount (result G legalL legalR defaultL hq e)
  positive e := LocalCompletionFamily.activeCount_positive _
  map e := LocalCompletionFamily.table (result G legalL legalR defaultL hq e)
  agrees e seed l :=
    ((result_correct G legalL legalR defaultL hq hsmall e).agrees seed
      (legalL (G.left e) l)
      ((input_mask_true G legalL legalR defaultL e _).2 ⟨l, rfl⟩)).trans
      (input_image_legal G legalL legalR defaultL e l)
  exact_two e seed b := by
    simpa only [← Nat.card_eq_fintype_card] using
      (result_correct G legalL legalR defaultL hq hsmall e).exact_two seed b
  illegal_probability e a b := by
    have hmask : (input G legalL legalR defaultL e).1 a.val ≠ true := by
      intro h
      exact a.property ((input_mask_true G legalL legalR defaultL e a.val).1 h)
    have h := (result_correct G legalL legalR defaultL hq hsmall e).illegal_probability
      a.val hmask b
    simpa only [Fintype.card_fin, card_legal] using h

@[simp] theorem family_size (hq : 0 < q)
    (hsmall : ∀ e b, Fintype.card {l : L (G.left e) // G.projection e l = b} ≤ 2) (e : E) :
    (family G legalL legalR defaultL hq hsmall).size e =
      LocalCompletionFamily.activeCount
        (LocalCompletionFamily.lookup hq (input G legalL legalR defaultL e)) := rfl

@[simp] theorem family_map (hq : 0 < q)
    (hsmall : ∀ e b, Fintype.card {l : L (G.left e) // G.projection e l = b} ≤ 2) (e : E) :
    (family G legalL legalR defaultL hq hsmall).map e =
      LocalCompletionFamily.table
        (LocalCompletionFamily.lookup hq (input G legalL legalR defaultL e)) := rfl

theorem family_size_le (hq : 0 < q)
    (hsmall : ∀ e b, Fintype.card {l : L (G.left e) // G.projection e l = b} ≤ 2) (e : E) :
    (family G legalL legalR defaultL hq hsmall).size e ≤ 2 * q :=
  LocalCompletionFamily.activeCount_le (result G legalL legalR defaultL hq e)

end
end PerfectCompleteness.LocalCompletionGame

end OAI
