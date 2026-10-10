import Mathlib

namespace OAI

/-!
# Port graphs, reduced walks, and capped-distance labels
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section

namespace DiscreteFree
open scoped BigOperators Classical

structure PortGraph (X D : Type*) where
  reverse : D → D
  reverse_involutive : Function.Involutive reverse
  move : X → D → X
  move_reverse : ∀ x e, move (move x e) (reverse e) = x

namespace PortGraph
variable {X D : Type*} (G : PortGraph X D)

def incidenceReverse : Equiv.Perm (X × D) :=
  (show Function.Involutive (fun z : X × D => (G.move z.1 z.2, G.reverse z.2)) from by
    rintro ⟨x, e⟩
    simp only [G.move_reverse, G.reverse_involutive e]).toPerm

@[simp] theorem incidenceReverse_apply (x : X) (e : D) :
    G.incidenceReverse (x, e) = (G.move x e, G.reverse e) := rfl

def walk (x : X) : List D → X
  | [] => x
  | e :: w => walk (G.move x e) w

@[simp] theorem walk_nil (x : X) : G.walk x [] = x := rfl
@[simp] theorem walk_cons (x : X) (e : D) (w : List D) :
    G.walk x (e::w) = G.walk (G.move x e) w := rfl

theorem walk_append (x : X) (u v : List D) :
    G.walk x (u ++ v) = G.walk (G.walk x u) v := by
  induction u generalizing x with
  | nil => rfl
  | cons e u ih => exact ih _

def Reduced (w : List D) : Prop := w.IsChain (fun e f => f ≠ G.reverse e)

def Near (n : ℕ) (x y : X) : Prop := ∃ w : List D, w.length ≤ n ∧ G.walk x w = y

theorem near_self (n : ℕ) (x : X) : G.Near n x x := ⟨[], by simp, rfl⟩

theorem near_mono {n m : ℕ} {x y : X} (hnm : n ≤ m) (h : G.Near n x y) :
    G.Near m x y := by
  obtain ⟨w, hw, rfl⟩ := h
  exact ⟨w, hw.trans hnm, rfl⟩

theorem near_step {n : ℕ} {x y : X} (e : D) (h : G.Near n (G.move x e) y) :
    G.Near (n+1) x y := by
  obtain ⟨w, hw, rfl⟩ := h
  exact ⟨e::w, by simpa using Nat.succ_le_succ hw, rfl⟩

def label {C : Type*} (color : X → C) (cap : ℕ) (i : C) (x : X) : ℕ :=
  Nat.find (show ∃ n : ℕ, n = cap ∨ ∃ w : List D,
    w.length = n ∧ color (G.walk x w) = i from ⟨cap, Or.inl rfl⟩)

theorem label_le {C : Type*} (color : X → C) (cap : ℕ) (i : C) (x : X) :
    G.label color cap i x ≤ cap := Nat.find_min' _ (Or.inl rfl)

theorem label_le_of_walk {C : Type*} (color : X → C) (cap : ℕ) (i : C)
    (x : X) (w : List D) (hw : color (G.walk x w) = i) :
    G.label color cap i x ≤ w.length := Nat.find_min' _ (Or.inr ⟨w, rfl, hw⟩)

@[simp] theorem label_own_color {C : Type*} (color : X → C) (cap : ℕ) (x : X) :
    G.label color cap (color x) x = 0 :=
  Nat.eq_zero_of_le_zero (G.label_le_of_walk color cap (color x) x [] rfl)

theorem label_witness {C : Type*} (color : X → C) (cap : ℕ) (i : C) (x : X)
    (h : G.label color cap i x < cap) :
    ∃ w : List D, w.length = G.label color cap i x ∧ color (G.walk x w) = i := by
  have hh := Nat.find_spec (show ∃ n : ℕ, n = cap ∨ ∃ w : List D,
    w.length = n ∧ color (G.walk x w) = i from ⟨cap, Or.inl rfl⟩)
  exact hh.resolve_left (Nat.ne_of_lt h)

theorem label_step_le {C : Type*} (color : X → C) (cap : ℕ) (i : C)
    (x : X) (e : D) :
    G.label color cap i x ≤ G.label color cap i (G.move x e) + 1 := by
  by_cases h : G.label color cap i (G.move x e) < cap
  · obtain ⟨w, hw, hc⟩ := G.label_witness color cap i (G.move x e) h
    have ht := G.label_le_of_walk color cap i x (e::w) hc
    simpa [hw] using ht
  · exact (G.label_le color cap i x).trans (by omega)

theorem label_step_abs {C : Type*} (color : X → C) (cap : ℕ) (i : C)
    (x : X) (e : D) :
    |(G.label color cap i x : ℝ) - G.label color cap i (G.move x e)| ≤ 1 := by
  have h₁ := G.label_step_le color cap i x e
  have h₂ := G.label_step_le color cap i (G.move x e) (G.reverse e)
  rw [G.move_reverse] at h₂
  rw [abs_le]
  have h₁' : (G.label color cap i x : ℝ) ≤ G.label color cap i (G.move x e) + 1 := by exact_mod_cast h₁
  have h₂' : (G.label color cap i (G.move x e) : ℝ) ≤ G.label color cap i x + 1 := by exact_mod_cast h₂
  constructor <;> linarith

end PortGraph

def BoundedWords (D : Type*) (n : ℕ) := {w : List D // w.length ≤ n}

instance {D : Type*} [Finite D] (n : ℕ) : Fintype (BoundedWords D n) :=
  (List.finite_length_le D n).fintype

namespace BoundedWords
variable {D : Type*}

def zeroEquiv : BoundedWords D 0 ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨[], le_rfl⟩
  left_inv w := Subtype.ext (by have := w.property; simp_all)
  right_inv _ := rfl

def succEquiv (n : ℕ) : BoundedWords D (n+1) ≃ Unit ⊕ (D × BoundedWords D n) where
  toFun w := match w with
    | ⟨[], _⟩ => Sum.inl ()
    | ⟨d::w, h⟩ => Sum.inr (d, ⟨w, Nat.le_of_succ_le_succ h⟩)
  invFun w := match w with
    | Sum.inl _ => ⟨[], by simp⟩
    | Sum.inr (d, w) => ⟨d::w.val, Nat.succ_le_succ w.property⟩
  left_inv w := by rcases w with ⟨(_|⟨d,w⟩),h⟩ <;> rfl
  right_inv w := by rcases w with (_|⟨d,w⟩) <;> rfl

@[simp] theorem card_zero [Finite D] : Fintype.card (BoundedWords D 0) = 1 := by
  simpa using Fintype.card_congr (zeroEquiv (D := D))

theorem card_succ [Fintype D] (n : ℕ) :
    Fintype.card (BoundedWords D (n+1)) =
      1 + Fintype.card D * Fintype.card (BoundedWords D n) := by
  simpa using Fintype.card_congr (succEquiv (D := D) n)

theorem card_lt_pow [Fintype D] (hD : 2 ≤ Fintype.card D) (n : ℕ) :
    Fintype.card (BoundedWords D n) < Fintype.card D ^ (n+1) := by
  induction n with
  | zero => simpa using (show 1 < Fintype.card D from hD)
  | succ n ih =>
    rw [card_succ, pow_succ]
    have hi : Fintype.card (BoundedWords D n) + 1 ≤ Fintype.card D ^ (n+1) := ih
    nlinarith

end BoundedWords

namespace PortGraph
variable {X D : Type*} [Fintype D] (G : PortGraph X D)

theorem near_finite (n : ℕ) (x : X) : {y : X | G.Near n x y}.Finite := by
  have h : {y : X | G.Near n x y} = Set.range
      (fun w : BoundedWords D n => G.walk x w.val) := by
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨w, hw⟩, rfl⟩
    · rintro ⟨⟨w, hw⟩, rfl⟩
      exact ⟨w, hw, rfl⟩
  rw [h]
  exact Set.finite_range _

theorem near_card_le (n : ℕ) (x : X) :
    Nat.card {y : X // G.Near n x y} ≤ Fintype.card (BoundedWords D n) := by
  let f : BoundedWords D n → {y : X // G.Near n x y} :=
    fun w => ⟨G.walk x w.val, w.val, w.property, rfl⟩
  have hf : Function.Surjective f := by
    rintro ⟨y, w, hw, rfl⟩
    exact ⟨⟨w, hw⟩, rfl⟩
  simpa only [Nat.card_eq_fintype_card] using Nat.card_le_card_of_surjective f hf

theorem label_support_le {C : Type*} [Fintype C] (color : X → C) (cap : ℕ)
    (x : X) : Nat.card {i : C // G.label color cap i x < cap} ≤
      Fintype.card (BoundedWords D cap) := by
  classical
  let f : {i : C // G.label color cap i x < cap} → BoundedWords D cap := fun i =>
    let w := (G.label_witness color cap i.val x i.property).choose
    ⟨w, by
      rw [(G.label_witness color cap i.val x i.property).choose_spec.1]
      exact G.label_le color cap i.val x⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    have hi := (G.label_witness color cap i.val x i.property).choose_spec.2
    have hj := (G.label_witness color cap j.val x j.property).choose_spec.2
    have he := congrArg (fun w : BoundedWords D cap => color (G.walk x w.val)) hij
    exact hi.symm.trans (he.trans hj)
  simpa only [Nat.card_eq_fintype_card] using Nat.card_le_card_of_injective f hf

end PortGraph
end DiscreteFree

end

end

end OAI
