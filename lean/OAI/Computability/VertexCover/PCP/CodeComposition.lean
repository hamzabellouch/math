import Mathlib
import OAI.Computability.VertexCover.Fourier.Walsh

namespace OAI

                                                                                        

noncomputable section

namespace UniqueGames.Foundations.PCP.CodeComposition

open scoped BigOperators
open UniqueGames.Foundations.Hastad

def disagreement (a b : Bool) : ℝ := if a = b then 0 else 1

@[simp] theorem disagreement_self (a : Bool) : disagreement a a = 0 := by
  simp [disagreement]

theorem disagreement_nonnegative (a b : Bool) : 0 ≤ disagreement a b := by
  cases a <;> cases b <;> norm_num [disagreement]

theorem disagreement_le_one (a b : Bool) : disagreement a b ≤ 1 := by
  cases a <;> cases b <;> norm_num [disagreement]

theorem disagreement_comm (a b : Bool) : disagreement a b = disagreement b a := by
  simp [disagreement, eq_comm]

theorem disagreement_triangle (a b «c» : Bool) :
    disagreement a «c» ≤ disagreement a b + disagreement b «c» := by
  cases a <;> cases b <;> cases «c» <;> norm_num [disagreement]

theorem disagreement_eq_sign (a b : Bool) :
    disagreement a b = (1 - bitSign a * bitSign b) / 2 := by
  cases a <;> cases b <;> norm_num [disagreement, bitSign]

def relativeDistance {X : Type*} [Fintype X] (f g : X → Bool) : ℝ :=
  𝔼 x, disagreement (f x) (g x)

@[simp] theorem relativeDistance_self {X : Type*} [Fintype X] (f : X → Bool) :
    relativeDistance f f = 0 := by
  simp [relativeDistance]

theorem relativeDistance_nonnegative {X : Type*} [Fintype X] (f g : X → Bool) :
    0 ≤ relativeDistance f g :=
  Finset.expect_nonneg (fun _ _ => disagreement_nonnegative _ _)

theorem relativeDistance_comm {X : Type*} [Fintype X] (f g : X → Bool) :
    relativeDistance f g = relativeDistance g f := by
  simp only [relativeDistance, disagreement_comm]

theorem relativeDistance_triangle {X : Type*} [Fintype X] (f g h : X → Bool) :
    relativeDistance f h ≤ relativeDistance f g + relativeDistance g h := by
  rw [relativeDistance, relativeDistance, relativeDistance,
    ← Finset.expect_add_distrib]
  exact Finset.expect_le_expect (fun _ _ => disagreement_triangle _ _ _)

theorem relativeDistance_eq_sign {X : Type*} [Fintype X] [Nonempty X]
    (f g : X → Bool) :
    relativeDistance f g = (1 - 𝔼 x, bitSign (f x) * bitSign (g x)) / 2 := by
  simp only [relativeDistance, disagreement_eq_sign]
  rw [← Finset.expect_div, Finset.expect_sub_distrib]
  simp

def codeword {A : Type*} (a : A) : Cube A → Bool := fun x => x a

private def singletonMask {A : Type*} [DecidableEq A] (a : A) : Cube A :=
  fun i => decide (i = a)

private theorem walsh_singletonMask {A : Type*} [Fintype A] [DecidableEq A]
    (a : A) (x : Cube A) : walsh (singletonMask a) x = bitSign (x a) := by
  classical
  unfold walsh singletonMask
  rw [Finset.prod_eq_single a]
  · simp
  · intro b _ hba
    simp [hba, bitSign]
  · simp

private theorem singletonMask_ne {A : Type*} [DecidableEq A] {a b : A} (hab : a ≠ b) :
    singletonMask a ≠ singletonMask b := by
  intro h
  have he := congrFun h a
  simp [singletonMask, hab] at he

theorem codeword_distance {A : Type*} [Fintype A] [DecidableEq A]
    {a b : A} (hab : a ≠ b) :
    relativeDistance (codeword a) (codeword b) = 1 / 2 := by
  rw [relativeDistance_eq_sign]
  have horth := walsh_orthogonality (singletonMask a) (singletonMask b)
  rw [ite_eq_right (singletonMask_ne hab)] at horth
  simp_rw [walsh_singletonMask] at horth
  change (1 - 𝔼 x : Cube A, bitSign (x a) * bitSign (x b)) / 2 = 1 / 2
  rw [horth]
  norm_num

theorem exists_nearest {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (f : Cube A → Bool) :
    ∃ a : A, ∀ b : A, relativeDistance f (codeword a) ≤ relativeDistance f (codeword b) := by
  classical
  obtain ⟨a, _, ha⟩ := Finset.exists_min_image Finset.univ
    (fun a : A => relativeDistance f (codeword a)) Finset.univ_nonempty
  exact ⟨a, fun b => ha b (Finset.mem_univ b)⟩

def nearest {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A] (f : Cube A → Bool) : A :=
  Classical.choose (exists_nearest f)

theorem nearest_minimal {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (f : Cube A → Bool) (a : A) :
    relativeDistance f (codeword (nearest f)) ≤ relativeDistance f (codeword a) :=
  Classical.choose_spec (exists_nearest f) a

theorem distance_from_other_codeword {A : Type*} [Fintype A] [DecidableEq A]
    [Nonempty A] (f : Cube A → Bool) {a : A} (ha : a ≠ nearest f) :
    1 / 4 ≤ relativeDistance f (codeword a) := by
  have htri := relativeDistance_triangle (codeword (nearest f)) f (codeword a)
  rw [codeword_distance (Ne.symm ha), relativeDistance_comm (codeword (nearest f)) f] at htri
  have hmin := nearest_minimal f a
  linarith

def pairWord {X : Type*} (left right : X → Bool) : Bool × X → Bool :=
  fun p => if p.1 then right p.2 else left p.2

theorem pairWord_distance {X : Type*} [Fintype X] [Nonempty X]
    (left right left' right' : X → Bool) :
    relativeDistance (pairWord left right) (pairWord left' right') =
      (relativeDistance left left' + relativeDistance right right') / 2 := by
  classical
  simp [relativeDistance, Fintype.expect_eq_sum_div_card, Fintype.card_prod,
    Fintype.sum_prod_type, pairWord]
  ring

theorem rejected_pair_far {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (accepts : A → A → Bool) (left right : Cube A → Bool)
    (hbad : accepts (nearest left) (nearest right) = false)
    (a b : A) (hgood : accepts a b = true) :
    1 / 8 ≤ relativeDistance (pairWord left right)
      (pairWord (codeword a) (codeword b)) := by
  rw [pairWord_distance]
  have hleft := relativeDistance_nonnegative left (codeword a)
  have hright := relativeDistance_nonnegative right (codeword b)
  by_cases ha : a = nearest left
  · have hb : b ≠ nearest right := by
      intro hb
      rw [ha, hb, hbad] at hgood
      cases hgood
    have hsep := distance_from_other_codeword right hb
    linarith
  · have hsep := distance_from_other_codeword left ha
    linarith

end UniqueGames.Foundations.PCP.CodeComposition
end

end OAI
