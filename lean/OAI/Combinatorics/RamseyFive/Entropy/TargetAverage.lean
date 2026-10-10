import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.OriginalMarginalLaw

namespace OAI

section
namespace SharpRamseyFive.TreeCodec
open FiniteEntropy BinaryTree
open scoped Classical BigOperators
variable {I Z X : Type*} [Fintype Z] [Fintype X]
lemma mean_pathBudget_twice (μ : Z → ℝ) (g : X → ℝ)
    (ρL ρR : Z → X → I → ℝ) (tree : BinaryTree I) (j : Address tree) :
    (∑ z, μ z * (∑ a, g a * pathBudget (ρL z a) (ρR z a) tree j)) =
      pathBudget (fun i => ∑ z, μ z * (∑ a, g a * ρL z a i))
        (fun i => ∑ z, μ z * (∑ a, g a * ρR z a i)) tree j := by
  simp_rw [mean_pathBudget g]
  exact mean_pathBudget μ _ _ tree j
end SharpRamseyFive.TreeCodec
namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {A : I → Type*} {B : J → Type*} [∀ i, Fintype (A i)] [∀ j, Fintype (B j)]
  {X Y : Type*} [Fintype X] [Fintype Y]

lemma original_target_mean_point (μ : ∀ i, Law (A i)) (ν : ∀ j, Law (B j))
    (j : J) (R : X → Y → Prop) (S : B j → Finset Y) (g : X → ℝ) (q : Y → ℝ)
    (C L : ℝ) (hC : 0≤C) (hg : ∀ a, 0≤g a)
    (hν : ∀ b, (∑ t, ν j t*uniformWeight (S t) b) ≤ L*q b) :
    (∑ z, originalLevelLaw μ ν z * (∑ a, g a*(C *
      relationMass (fun b a => R a b) (uniformWeight (S (z.2 j))) (uniformWeight {a})))) ≤
        C*L*relationMass R g q := by
  have he (z : (∀ i, A i) × (∀ j, B j)) :
      (∑ a, g a*(C*relationMass (fun b a => R a b) (uniformWeight (S (z.2 j))) (uniformWeight {a}))) =
        C*relationMass R g (uniformWeight (S (z.2 j))) := by
    rw [← relationMass_swap R g, ← relationMass_weighted_singleton]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  simp_rw [he]
  calc
    _ = C*(∑ z, originalLevelLaw μ ν z*relationMass R g (uniformWeight (S (z.2 j)))) := by
      simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intro z _; ring
    _ ≤ C*(L*relationMass R g q) :=
      mul_le_mul_of_nonneg_left (originalLevelLaw_right_domination μ ν j R S g q L hg hν) hC
    _ = _ := by ring

lemma original_target_mean_dual (μ : ∀ i, Law (A i)) (ν : ∀ j, Law (B j))
    (i : I) (R : X → Y → Prop) (S : A i → Finset X) (p : X → ℝ) (g : Y → ℝ)
    (C L : ℝ) (hC : 0≤C) (hg : ∀ b, 0≤g b)
    (hμ : ∀ a, (∑ t, μ i t*uniformWeight (S t) a) ≤ L*p a) :
    (∑ z, originalLevelLaw μ ν z * (∑ b, g b*(C *
      relationMass R (uniformWeight (S (z.1 i))) (uniformWeight {b})))) ≤
        C*L*relationMass R p g := by
  have he (z : (∀ i, A i) × (∀ j, B j)) :
      (∑ b, g b*(C*relationMass R (uniformWeight (S (z.1 i))) (uniformWeight {b}))) =
        C*relationMass R (uniformWeight (S (z.1 i))) g := by
    rw [← relationMass_weighted_singleton R _ g]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  simp_rw [he]
  calc
    _ = C*(∑ z, originalLevelLaw μ ν z*relationMass R (uniformWeight (S (z.1 i))) g) := by
      simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intro z _; ring
    _ ≤ C*(L*relationMass R p g) :=
      mul_le_mul_of_nonneg_left (originalLevelLaw_left_domination μ ν i R S p g L hg hμ) hC
    _ = _ := by ring
end SharpRamseyFive.FiniteEntropy

end

namespace SharpRamseyFive.TreeCodec
open FiniteEntropy BinaryTree
open scoped Classical BigOperators
variable {I Z A : Type*} [Fintype Z] [Fintype A]
lemma mean_two_pathBudget_scaled (μ : Z → ℝ) (g : A → ℝ)
    (ρL ρR : Z → A → I → ℝ) (c : ℝ) (tree : BinaryTree I) (j : Address tree) :
    (∑ z, μ z*(∑ a, g a*(c*pathBudget (ρL z a) (ρR z a) tree j))) =
      c*pathBudget (fun i => ∑ z, μ z*(∑ a, g a*ρL z a i))
        (fun i => ∑ z, μ z*(∑ a, g a*ρR z a i)) tree j := by
  rw [← mean_pathBudget_twice]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro a _
  ring
end SharpRamseyFive.TreeCodec

end OAI
