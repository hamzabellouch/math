import Mathlib

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage.Partitions
open Finset

variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

def hit (H : A → Finset B) : Finset (A → B) :=
  univ.filter (fun w => ∃ a, w a ∈ H a)

def avoid (H : A → Finset B) : Finset (A → B) :=
  univ.filter (fun w => ∀ a, w a ∉ H a)

@[simp] theorem mem_hit (H : A → Finset B) (w : A → B) :
    w ∈ hit H ↔ ∃ a, w a ∈ H a := by simp [hit]

@[simp] theorem mem_avoid (H : A → Finset B) (w : A → B) :
    w ∈ avoid H ↔ ∀ a, w a ∉ H a := by simp [avoid]

def avoidEquiv (H : A → Finset B) :
    {w : A → B // ∀ a, w a ∉ H a} ≃ ((a : A) → {b : B // b ∉ H a}) where
  toFun w a := ⟨w.val a,w.property a⟩
  invFun w := ⟨fun a => (w a).val,fun a => (w a).property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem avoid_card (H : A → Finset B) :
    (avoid H).card = ∏ a, (Fintype.card B - (H a).card) := by
  have h := Fintype.card_congr (avoidEquiv H)
  rw [Fintype.card_pi] at h
  have hb (a : A) : Fintype.card {b : B // b ∉ H a} = Fintype.card B - (H a).card := by
    rw [Fintype.card_subtype_compl]
    simp
  simp only [hb] at h
  rw [Fintype.card_subtype] at h
  exact h

theorem hit_add_avoid (H : A → Finset B) :
    (hit H).card+(avoid H).card = Fintype.card B ^ Fintype.card A := by
  have hm : avoid H = (hit H)ᶜ := by
    ext w
    simp
  rw [hm,Finset.card_compl]
  have hn : (hit H).card ≤ Fintype.card (A → B) := Finset.card_le_univ _
  rw [Fintype.card_fun] at hn ⊢
  omega

def active (H : A → Finset B) : Finset A := univ.filter (fun a => (H a).Nonempty)

omit [Fintype B] [DecidableEq A] [DecidableEq B] in
@[simp] theorem mem_active (H : A → Finset B) (a : A) :
    a ∈ active H ↔ (H a).Nonempty := by simp [active]

theorem functional_avoid_card (H : A → Finset B) (h : ∀ a, (H a).card ≤ 1) :
    (avoid H).card = (Fintype.card B-1)^(active H).card *
      (Fintype.card B)^(Fintype.card A-(active H).card) := by
  rw [avoid_card]
  have hc (a : A) : Fintype.card B-(H a).card =
      if a ∈ active H then Fintype.card B-1 else Fintype.card B := by
    split_ifs with ha
    · have hp := Finset.card_pos.mpr ((mem_active H a).mp ha)
      have he : (H a).card = 1 := by have hh := h a; omega
      rw [he]
    · have hz : (H a).card = 0 := by
        exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp
          (fun hn => ha ((mem_active H a).mpr hn)))
      rw [hz,Nat.sub_zero]
  simp only [hc]
  have ht : univ.filter (fun a => a ∈ active H) = active H := by ext a; simp
  have hf : univ.filter (fun a => a ∉ active H) = (active H)ᶜ := by ext a; simp
  rw [Finset.prod_ite,ht,hf,Finset.prod_const,Finset.prod_const,Finset.card_compl]

theorem functional_hit_real (H : A → Finset B) (hB : 0 < Fintype.card B)
    (h : ∀ a, (H a).card ≤ 1) :
    ((hit H).card : ℝ) = (Fintype.card B : ℝ)^Fintype.card A *
      (1-(1-1/(Fintype.card B : ℝ))^(active H).card) := by
  have hh := hit_add_avoid H
  have hav := functional_avoid_card H h
  have hq : (active H).card ≤ Fintype.card A := Finset.card_le_univ _
  have hd : (Fintype.card B : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hB
  have hscalar : (Fintype.card B:ℝ)*(1-1/(Fintype.card B:ℝ)) = Fintype.card B-1 := by
    field_simp
  have heq : (Fintype.card B:ℝ)^Fintype.card A *
      (1-1/(Fintype.card B:ℝ))^(active H).card =
      (Fintype.card B-1:ℝ)^(active H).card *
        (Fintype.card B:ℝ)^(Fintype.card A-(active H).card) := by
    rw [← hscalar,mul_pow]
    calc
      _ = (Fintype.card B:ℝ)^((active H).card+(Fintype.card A-(active H).card))*
          (1-1/(Fintype.card B:ℝ))^(active H).card := by rw [Nat.add_sub_of_le hq]
      _ = _ := by rw [pow_add]; ring
  have hr : ((hit H).card:ℝ) + ((avoid H).card:ℝ) =
      (Fintype.card B:ℝ)^Fintype.card A := by exact_mod_cast hh
  have hv : ((avoid H).card:ℝ) =
      (Fintype.card B-1:ℝ)^(active H).card *
        (Fintype.card B:ℝ)^(Fintype.card A-(active H).card) := by
    rw [hav]
    push_cast
    rw [Nat.cast_sub (by omega : 1 ≤ Fintype.card B)]
    norm_num
  rw [← heq] at hv
  nlinarith

end MetricKMedian.Coverage.Partitions

end Inline_PCPInherited

end OAI
