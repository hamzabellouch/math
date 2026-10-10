import Mathlib
import OAI.Combinatorics.RamseyFive.Trees.TreeOriginalTrims

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {α : Type*} [Fintype α]

noncomputable def positiveLaw (p : Law α) : Law {a // 0 < p a} where
  mass a := p a
  nonneg a := p.nonneg a
  sum_one := by
    rw [← Finset.sum_subtype (Finset.univ.filter (fun a => 0 < p a)) (by simp), Finset.sum_filter]
    calc
      _ = ∑ a, p a := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases h : 0 < p a
        · simp [h]
        · have hz : p a = 0 := le_antisymm (le_of_not_gt h) (p.nonneg a)
          simp [hz]
      _ = 1 := p.sum_one

lemma positiveLaw_mean (p : Law α) (f : α → ℝ) :
    (∑ a, positiveLaw p a * f a) = ∑ a, p a * f a := by
  change (∑ a : {a // 0 < p a}, p a * f a) = _
  rw [← Finset.sum_subtype (Finset.univ.filter (fun a => 0 < p a)) (by simp) (fun a => p a * f a), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : 0 < p a
  · simp [h]
  · have hz : p a = 0 := le_antisymm (le_of_not_gt h) (p.nonneg a)
    simp [hz]

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {A : I → Type*} {B : J → Type*} [∀ i, Fintype (A i)] [∀ j, Fintype (B j)]

noncomputable def originalLevelLaw (μ : ∀ i, Law (A i)) (ν : ∀ j, Law (B j)) :
    Law ((∀ i, A i) × (∀ j, B j)) :=
  adaptiveLaw (piLaw μ) (fun _ => piLaw ν)

lemma originalLevelLaw_cross_mean (μ : ∀ i, Law (A i)) (ν : ∀ j, Law (B j))
    (i : I) (j : J) (f : A i → B j → ℝ) :
    (∑ z, originalLevelLaw μ ν z * f (z.1 i) (z.2 j)) =
      ∑ a, ∑ b, μ i a * ν j b * f a b := by
  rw [originalLevelLaw, sum_adaptive]
  simp_rw [piLaw_eval_expectation ν j]
  rw [piLaw_eval_expectation μ i (fun a => ∑ b, ν j b * f a b)]
  simp only [Finset.mul_sum, mul_assoc]

lemma originalLevelLaw_cross_domination {X Y : Type*} [Fintype X] [Fintype Y]
    (μ : ∀ i, Law (A i)) (ν : ∀ j, Law (B j))
    (i : I) (j : J) (R : X → Y → Prop) (s : A i → Finset X) (t : B j → Finset Y)
    (p : Law X) (q : Law Y) (L : ℝ) (hL : 0 ≤ L)
    (hs : ∀ x, (∑ a, μ i a * uniformWeight (s a) x) ≤ L * p x)
    (ht : ∀ y, (∑ b, ν j b * uniformWeight (t b) y) ≤ L * q y) :
    (∑ z, originalLevelLaw μ ν z *
      relationMass R (uniformWeight (s (z.1 i))) (uniformWeight (t (z.2 j)))) ≤
        L^2 * relationMass R p q := by
  rw [originalLevelLaw_cross_mean μ ν i j (fun a b => relationMass R (uniformWeight (s a)) (uniformWeight (t b)))]
  exact independent_support_domination R p q (μ i) (ν j) s t L hL hs ht

end SharpRamseyFive.FiniteEntropy
namespace SharpRamseyFive.TreeCodec
open FiniteEntropy BinaryTree
open scoped Classical BigOperators
variable {I W : Type*} [Fintype W]
lemma mean_pathBudget (p : W → ℝ) (ρL ρR : W → I → ℝ)
    (b : BinaryTree I) (j : Address b) :
    (∑ ω, p ω * pathBudget (ρL ω) (ρR ω) b j) =
      pathBudget (fun i => ∑ ω, p ω * ρL ω i) (fun i => ∑ ω, p ω * ρR ω i) b j := by
  induction b with
  | nil => exact nomatch j
  | node i l r ihl ihr =>
    rcases j with j | (j | j)
    · simp only [pathBudget, mul_zero, Finset.sum_const_zero]
    · simp only [pathBudget, mul_add, Finset.sum_add_distrib, ihl]
    · simp only [pathBudget, mul_add, Finset.sum_add_distrib, ihr]

lemma pathBudget_mono (ρL ρR τL τR : I → ℝ)
    (hL : ∀ i, ρL i ≤ τL i) (hR : ∀ i, ρR i ≤ τR i)
    (b : BinaryTree I) (j : Address b) :
    pathBudget ρL ρR b j ≤ pathBudget τL τR b j := by
  induction b with
  | nil => exact nomatch j
  | node i l r ihl ihr =>
    rcases j with j | (j | j)
    · rfl
    · exact add_le_add (hL i) (ihl j)
    · exact add_le_add (hR i) (ihr j)

lemma pathBudget_const_le_height (a : ℝ) (ha : 0 ≤ a) (b : BinaryTree I) (j : Address b) :
    pathBudget (fun _ => a) (fun _ => a) b j ≤ b.height * a := by
  have h : pathBudget (fun _ => a) (fun _ => a) b j ≤ pathSum b (fun _ => a) j := by
    induction b with
    | nil => exact nomatch j
    | node i l r ihl ihr =>
      rcases j with j | (j | j)
      · exact ha
      · exact add_le_add le_rfl (ihl j)
      · exact add_le_add le_rfl (ihr j)
  exact h.trans (pathSum_const_le_height b j a ha)
end SharpRamseyFive.TreeCodec

end OAI
