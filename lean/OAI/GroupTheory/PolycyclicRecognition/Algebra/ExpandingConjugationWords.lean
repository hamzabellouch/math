import OAI.GroupTheory.PolycyclicRecognition.Algebra.ComplexBinaryWords
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialGrowthNoFreePair
import Mathlib.GroupTheory.GroupAction.ConjAct

namespace OAI

/-! # Expanding conjugation creates exponentially many short words

The character is an additive-valued homomorphism on a normal subgroup.
Its expansion separates binary words in conjugates of a single element.
-/

noncomputable section
namespace PolycyclicRecognition

def conjugationBinaryWord {N : Type*} [Group N] (a : MulAut N) (x : N) : List Bool → N
  | [] => 1
  | b :: l => (if b then x else 1) * a (conjugationBinaryWord a x l)

theorem conjugationBinaryWord_character {N : Type*} [Group N]
    (a : MulAut N) (x : N) (χ : N →* Multiplicative ℂ) (z : ℂ)
    (hχ : ∀ y, (χ (a y)).toAdd = z * (χ y).toAdd) (l : List Bool) :
    (χ (conjugationBinaryWord a x l)).toAdd =
      (χ x).toAdd * complexBinaryWord z l := by
  induction l with
  | nil => simp [conjugationBinaryWord, complexBinaryWord]
  | cons b l ih =>
    simp only [conjugationBinaryWord, map_mul, toAdd_mul, hχ, ih,
      complexBinaryWord]
    cases b <;> simp [complexBit] <;> ring

theorem conjugationBinaryWord_injective_length {N : Type*} [Group N]
    (a : MulAut N) (x : N) (χ : N →* Multiplicative ℂ) (z : ℂ)
    (hχ : ∀ y, (χ (a y)).toAdd = z * (χ y).toAdd)
    (hx : (χ x).toAdd ≠ 0) (hz : 2 ≤ ‖z‖)
    {l k : List Bool} (hlen : l.length = k.length)
    (he : conjugationBinaryWord a x l = conjugationBinaryWord a x k) : l = k := by
  have h := congrArg (fun y => (χ y).toAdd) he
  rw [conjugationBinaryWord_character a x χ z hχ,
    conjugationBinaryWord_character a x χ z hχ] at h
  exact complexBinaryWord_injective_length hz hlen (mul_left_cancel₀ hx h)

variable {G : Type*} [Group G] [DecidableEq G]

theorem conjugationBinaryWord_word_bound
    (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (N : Subgroup G) [N.Normal] (t : G) (x : N) (m : ℕ)
    (ht : t ∈ wordBall S m) (hx : (x : G) ∈ wordBall S m) (l : List Bool) :
    (conjugationBinaryWord (N := N) (MulAut.conjNormal t) x l : G) ∈
      wordBall S (3 * m * l.length) := by
  induction l with
  | nil => simp [conjugationBinaryWord]
  | cons b l ih =>
    have hb : (if b then (x : G) else 1) ∈ wordBall S m := by
      cases b
      · exact one_mem_wordBall S m
      · exact hx
    have h := mul_mem_wordBall hb
      (mul_mem_wordBall (mul_mem_wordBall ht ih) (inv_mem_wordBall hS ht))
    simpa only [conjugationBinaryWord, Subgroup.coe_mul, MulAut.conjNormal_apply,
      apply_ite, Subgroup.coe_one, List.length_cons,
      show m + (m + 3 * m * l.length + m) = 3 * m * (l.length + 1) by ring] using h

theorem expanding_conjugation_exponential_count
    (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (N : Subgroup G) [N.Normal] (t : G) (x : N) (m : ℕ)
    (ht : t ∈ wordBall S m) (hx : (x : G) ∈ wordBall S m)
    (χ : N →* Multiplicative ℂ) (z : ℂ)
    (hχ : ∀ y, (χ (MulAut.conjNormal t y)).toAdd = z * (χ y).toAdd)
    (hxχ : (χ x).toAdd ≠ 0) (hz : 2 ≤ ‖z‖) (n : ℕ) :
    2 ^ n ≤ (wordBall S (3 * m * n)).card := by
  classical
  let f : (Fin n → Bool) → G := fun b =>
    conjugationBinaryWord (N := N) (MulAut.conjNormal t) x (List.ofFn b)
  have hf : Function.Injective f := by
    intro a b hab
    apply List.ofFn_injective
    apply conjugationBinaryWord_injective_length (MulAut.conjNormal t) x χ z hχ hxχ hz
      (by simp)
    exact Subtype.ext hab
  let A := Finset.univ.image f
  have hA : A ⊆ wordBall S (3 * m * n) := by
    intro g hg
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hg
    simpa only [f, List.length_ofFn] using
      conjugationBinaryWord_word_bound S hS N t x m ht hx (List.ofFn b)
  calc
    2 ^ n = A.card := by simp [A, Finset.card_image_of_injective _ hf]
    _ ≤ _ := Finset.card_le_card hA

theorem polynomial_growth_no_expanding_conjugation
    (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hvol : ∃ C d : ℕ, ∀ n, (wordBall S n).card ≤ C * (1 + n) ^ d)
    (N : Subgroup G) [N.Normal] (t : G) (x : N)
    (χ : N →* Multiplicative ℂ) (z : ℂ)
    (hχ : ∀ y, (χ (MulAut.conjNormal t y)).toAdd = z * (χ y).toAdd)
    (hxχ : (χ x).toAdd ≠ 0) : ‖z‖ < 2 := by
  by_contra! hz
  obtain ⟨a, ha⟩ := wordBall_exhaustive S hS hgen t
  obtain ⟨b, hb⟩ := wordBall_exhaustive S hS hgen (x : G)
  let m := max a b
  exact polynomial_word_growth_not_exponential S hvol (3 * m)
    (expanding_conjugation_exponential_count S hS N t x m
      (wordBall_mono S (le_max_left _ _) ha)
      (wordBall_mono S (le_max_right _ _) hb) χ z hχ hxχ hz)

end PolycyclicRecognition

end

end OAI
