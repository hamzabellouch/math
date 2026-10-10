import OAI.Combinatorics.CliqueFree.Model

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence
universe u
namespace Lottery
variable {α β : Type u}

/-- A finite real lottery; list entries need not have distinct outcomes. -/
abbrev Law (α : Type u) := List (ℝ × α)

def expect (L : Law α) (f : α → ℝ) : ℝ := (L.map fun z ↦ z.1 * f z.2).sum

def Positive (L : Law α) : Prop := ∀ z ∈ L, 0 ≤ z.1

def total (L : Law α) : ℝ := expect L (fun _ ↦ 1)

def IsProb (L : Law α) : Prop := Positive L ∧ total L = 1

@[simp] lemma expect_nil (f : α → ℝ) : expect [] f = 0 := rfl
@[simp] lemma expect_cons (p : ℝ) (a : α) (L : Law α) (f : α → ℝ) :
    expect ((p,a)::L) f = p*f a + expect L f := rfl
@[simp] lemma expect_singleton (p : ℝ) (a : α) (f : α → ℝ) : expect [(p,a)] f = p*f a := by
  simp [expect]

lemma expect_append (L K : Law α) (f : α → ℝ) : expect (L++K) f = expect L f + expect K f := by
  simp [expect]

lemma expect_add (L : Law α) (f g : α → ℝ) :
    expect L (fun a ↦ f a + g a) = expect L f + expect L g := by
  induction L with
  | nil => simp
  | cons z L ih =>
    rcases z with ⟨p,a⟩
    simp only [expect_cons,ih]
    ring

lemma expect_mul (L : Law α) (a : ℝ) (f : α → ℝ) :
    expect L (fun z ↦ a*f z) = a * expect L f := by
  induction L with
  | nil => simp
  | cons z L ih =>
    rcases z with ⟨p,a⟩
    simp only [expect_cons,ih]
    ring

lemma expect_const (L : Law α) (a : ℝ) : expect L (fun _ ↦ a) = a * total L := by
  simpa only [mul_one,total] using expect_mul L a (fun _ ↦ 1)

lemma expect_mono {L : Law α} (hL : Positive L) {f g : α → ℝ}
    (h : ∀ z ∈ L, f z.2 ≤ g z.2) : expect L f ≤ expect L g := by
  induction L with
  | nil => rfl
  | cons z L ih =>
    exact add_le_add (mul_le_mul_of_nonneg_left (h z (by simp)) (hL z (by simp)))
      (ih (fun t ht ↦ hL t (by simp [ht])) (fun t ht ↦ h t (by simp [ht])))

lemma expect_sum {I : Type*} (L : Law α) (s : Finset I) (f : I → α → ℝ) :
    expect L (fun a ↦ ∑ i ∈ s, f i a) = ∑ i ∈ s, expect L (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [expect_const]
  | @insert i s hi ih => simp only [sum_insert hi,expect_add,ih]

def transform (p : ℝ) (f : α → β) (L : Law α) : Law β := L.map (fun z ↦ (p*z.1,f z.2))

lemma expect_transform (p : ℝ) (f : α → β) (L : Law α) (g : β → ℝ) :
    expect (transform p f L) g = p * expect L (g ∘ f) := by
  induction L with
  | nil => simp [transform]
  | cons z L ih =>
    rcases z with ⟨q,a⟩
    simp only [transform,List.map_cons,expect_cons,Function.comp_apply] at *
    rw [ih]
    ring

lemma total_transform (p : ℝ) (f : α → β) (L : Law α) :
    total (transform p f L) = p * total L := expect_transform _ _ _ _

lemma positive_transform {p : ℝ} (hp : 0 ≤ p) (f : α → β) {L : Law α} (hL : Positive L) :
    Positive (transform p f L) := by
  intro z hz
  obtain ⟨y,hy,rfl⟩ := List.mem_map.1 hz
  exact mul_nonneg hp (hL y hy)

lemma positive_append {L K : Law α} (hL : Positive L) (hK : Positive K) : Positive (L++K) := by
  intro z hz
  rcases List.mem_append.1 hz with hz | hz
  · exact hL z hz
  · exact hK z hz

end Lottery

end CliqueFreeIndependence

end

end OAI
