import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialGrowthNoFreePair
import Mathlib.GroupTheory.GroupAction.Defs

namespace OAI

/-! # Polynomial growth excludes one-sided ping-pong

Equal-length positive words suffice for the exponential word-ball count.
No control of the inverse transformations is required.
-/

noncomputable section
namespace PolycyclicRecognition
open Finset

theorem positive_word_preserves_domain
    {G X : Type*} [Group G] [MulAction G X] (a : Bool → G)
    (D : Set X) (ha : ∀ i x, x ∈ D → a i • x ∈ D)
    (l : List Bool) {x : X} (hx : x ∈ D) : (l.map a).prod • x ∈ D := by
  induction l with
  | nil => simpa using hx
  | cons i l ih =>
    simpa only [List.map_cons, List.prod_cons, mul_smul] using ha i _ ih

theorem one_sided_ping_pong_equal_length
    {G X : Type*} [Group G] [MulAction G X] (a : Bool → G) (P : Bool → Set X)
    (hP : Disjoint (P false) (P true)) (hne : (P false).Nonempty)
    (ha : ∀ i x, x ∈ P false ∪ P true → a i • x ∈ P i)
    (l k : List Bool) (hlen : l.length = k.length)
    (he : (l.map a).prod = (k.map a).prod) : l = k := by
  have hpres (i : Bool) (x : X) (hx : x ∈ P false ∪ P true) :
      a i • x ∈ P false ∪ P true := by
    have hh := ha i x hx
    cases i
    · exact Or.inl hh
    · exact Or.inr hh
  induction l generalizing k with
  | nil => simpa using hlen.symm
  | cons i l ih =>
    cases k with
    | nil => simp at hlen
    | cons j k =>
      have hij : i = j := by
        obtain ⟨x, hx⟩ := hne
        have hl := ha i _ (positive_word_preserves_domain a _ hpres l (Or.inl hx))
        have hk := ha j _ (positive_word_preserves_domain a _ hpres k (Or.inl hx))
        have hs : a i • ((l.map a).prod • x) = a j • ((k.map a).prod • x) := by
          simpa only [List.map_cons, List.prod_cons, mul_smul] using
            congrArg (fun g : G => g • x) he
        rw [hs] at hl
        cases i <;> cases j
        · rfl
        · exact False.elim (Set.disjoint_left.mp hP hl hk)
        · exact False.elim (Set.disjoint_left.mp hP hk hl)
        · rfl
      subst j
      have he' : (l.map a).prod = (k.map a).prod :=
        mul_left_cancel (by simpa only [List.map_cons, List.prod_cons] using he)
      exact congrArg (List.cons i) (ih k (Nat.succ.inj hlen) he')

theorem one_sided_ping_pong_exponential_word_count
    {G X : Type*} [Group G] [DecidableEq G] [MulAction G X]
    (S : Finset G) (a : Bool → G) (P : Bool → Set X)
    (hP : Disjoint (P false) (P true)) (hne : (P false).Nonempty)
    (ha : ∀ i x, x ∈ P false ∪ P true → a i • x ∈ P i)
    (m : ℕ) (hm : ∀ i, a i ∈ wordBall S m) (n : ℕ) :
    2 ^ n ≤ (wordBall S (m * n)).card := by
  classical
  have hw (l : List Bool) : (l.map a).prod ∈ wordBall S (m * l.length) := by
    induction l with
    | nil => simp
    | cons i l ih =>
      simpa only [List.map_cons, List.prod_cons, List.length_cons,
        Nat.mul_add, Nat.mul_one, Nat.add_comm] using mul_mem_wordBall (hm i) ih
  let f : (Fin n → Bool) → G := fun w => ((List.ofFn w).map a).prod
  have hf : Function.Injective f := by
    intro w v he
    apply List.ofFn_injective
    exact one_sided_ping_pong_equal_length a P hP hne ha _ _ (by simp) he
  let A := Finset.univ.image f
  have hA : A ⊆ wordBall S (m * n) := by
    intro x hx
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hx
    simpa only [List.length_ofFn] using hw (List.ofFn w)
  calc
    2 ^ n = A.card := by simp [A, Finset.card_image_of_injective _ hf]
    _ ≤ _ := Finset.card_le_card hA

theorem polynomial_growth_excludes_one_sided_ping_pong
    {G X : Type*} [Group G] [DecidableEq G] [MulAction G X]
    (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hvol : ∃ C d : ℕ, ∀ n, (wordBall S n).card ≤ C * (1 + n) ^ d)
    (a : Bool → G) (P : Bool → Set X)
    (hP : Disjoint (P false) (P true)) (hne : (P false).Nonempty)
    (ha : ∀ i x, x ∈ P false ∪ P true → a i • x ∈ P i) : False := by
  obtain ⟨m₀, hm₀⟩ := wordBall_exhaustive S hS hgen (a false)
  obtain ⟨m₁, hm₁⟩ := wordBall_exhaustive S hS hgen (a true)
  let m := max m₀ m₁
  have hm (i : Bool) : a i ∈ wordBall S m := by
    cases i
    · exact wordBall_mono S (le_max_left _ _) hm₀
    · exact wordBall_mono S (le_max_right _ _) hm₁
  exact polynomial_word_growth_not_exponential S hvol m
    (one_sided_ping_pong_exponential_word_count S a P hP hne ha m hm)

end PolycyclicRecognition

end

end OAI
