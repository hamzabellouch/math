import OAI.Probability.Ising.Basic

namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

lemma spin_not (s : Bool) : spin (!s) = -spin s := by
  cases s <;> norm_num [spin]

lemma spin_sq (s : Bool) : spin s * spin s = 1 := by
  cases s <;> norm_num [spin]

/-- A coloring is constant on precisely the components specified by a setoid. -/
def Respects {V : Type*} (S : Setoid V) (σ : V → Bool) : Prop :=
  ∀ x y, S.r x y → σ x = σ y

abbrev Colorings {V : Type*} (S : Setoid V) := {σ : V → Bool // Respects S σ}

noncomputable instance coloringsFintype {V : Type*} [Fintype V] (S : Setoid V) :
    Fintype (Colorings S) := Fintype.ofFinite _

/-- The exact bijection underlying the factor 2^(number of FK clusters). -/
def componentColoringEquiv {V : Type*} (S : Setoid V) :
    Colorings S ≃ (Quotient S → Bool) where
  toFun σ := Quotient.lift σ.val σ.property
  invFun c := ⟨fun x => c (Quotient.mk S x), fun _ _ h => congrArg c (Quotient.sound h)⟩
  left_inv σ := by apply Subtype.ext; rfl
  right_inv c := by
    funext q
    induction q using Quotient.inductionOn with | _ x => rfl

lemma card_colorings {V : Type*} [Fintype V] (S : Setoid V) :
    Fintype.card (Colorings S) = 2 ^ Nat.card (Quotient S) := by
  classical
  rw [Fintype.card_congr (componentColoringEquiv S), Fintype.card_fun]
  simp [Nat.card_eq_fintype_card]

noncomputable def flipAt {V : Type*} (x : V) : (V → Bool) ≃ (V → Bool) := by
  classical
  let f := fun (σ : V → Bool) y => if y = x then !(σ y) else σ y
  have hf : Function.Involutive f := by
    intro σ
    funext y
    dsimp [f]
    by_cases h : y = x <;> simp [h]
  exact hf.toPerm f

lemma flipAt_apply {V : Type*} (x y : V) (σ : V → Bool) :
    flipAt x σ y = if y = x then !(σ y) else σ y := by
  classical
  rfl

lemma sum_spin_product {V : Type*} [Fintype V] [DecidableEq V] (x y : V) :
    (∑ σ : V → Bool, spin (σ x) * spin (σ y)) =
      if x = y then (2 : ℝ) ^ Fintype.card V else 0 := by
  classical
  by_cases hxy : x = y
  · subst y
    simp [spin_sq]
  · simp only [hxy, ite_false]
    have H := (flipAt x).sum_comp (fun σ => spin (σ x) * spin (σ y))
    have hf : ∀ σ, spin (flipAt x σ x) * spin (flipAt x σ y) =
        -(spin (σ x) * spin (σ y)) := by
      intro σ
      simp [flipAt_apply, Ne.symm hxy, spin_not]
    simp only [hf, Finset.sum_neg_distrib] at H
    linarith

lemma sum_if_respects {V : Type*} [Fintype V] [DecidableEq V] (S : Setoid V) (f : (V → Bool) → ℝ) :
    (∑ σ, if Respects S σ then f σ else 0) = ∑ σ : Colorings S, f σ.val := by
  classical
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) f

lemma sum_respects_one {V : Type*} [Fintype V] [DecidableEq V] (S : Setoid V) :
    (∑ σ : V → Bool, if Respects S σ then (1 : ℝ) else 0) =
      2 ^ Nat.card (Quotient S) := by
  classical
  rw [sum_if_respects]
  simp [card_colorings]

lemma sum_respects_spin_product {V : Type*} [Fintype V] [DecidableEq V]
    (S : Setoid V) (x y : V) :
    (∑ σ : V → Bool, if Respects S σ then spin (σ x) * spin (σ y) else 0) =
      if S.r x y then (2 : ℝ) ^ Nat.card (Quotient S) else 0 := by
  classical
  rw [sum_if_respects]
  rw [Fintype.sum_equiv (componentColoringEquiv S)
    (fun σ : Colorings S => spin (σ.val x) * spin (σ.val y))
    (fun c => spin (c (Quotient.mk S x)) * spin (c (Quotient.mk S y))) (by intro σ; rfl)]
  simpa only [Nat.card_eq_fintype_card, Quotient.eq] using
    sum_spin_product (Quotient.mk S x) (Quotient.mk S y)

lemma respects_eqvGen {V : Type*} (R : V → V → Prop) (σ : V → Bool) :
    Respects (Relation.EqvGen.setoid R) σ ↔ ∀ x y, R x y → σ x = σ y := by
  constructor
  · intro h x y hxy
    exact h x y (Relation.EqvGen.rel x y hxy)
  · intro h x y hxy
    induction hxy with
    | rel x y hxy => exact h x y hxy
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

end BufferedIsing

end OAI
