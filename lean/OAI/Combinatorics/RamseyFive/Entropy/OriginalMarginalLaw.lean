import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.LevelTreeTrims

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {A : I → Type*} {B : J → Type*} [∀ i, Fintype (A i)] [∀ j, Fintype (B j)]
lemma originalLevelLaw_first_mean (μ : ∀ i, Law (A i)) (ν : ∀ j, Law (B j))
    (i : I) (f : A i → ℝ) :
    (∑ z, originalLevelLaw μ ν z*f (z.1 i)) = ∑ a, μ i a*f a := by
  rw [originalLevelLaw, sum_adaptive]
  simp only [← Finset.sum_mul, (piLaw ν).sum_one, one_mul]
  exact piLaw_eval_expectation μ i f

lemma originalLevelLaw_second_mean (μ : ∀ i, Law (A i)) (ν : ∀ j, Law (B j))
    (j : J) (f : B j → ℝ) :
    (∑ z, originalLevelLaw μ ν z*f (z.2 j)) = ∑ b, ν j b*f b := by
  rw [originalLevelLaw, sum_adaptive]
  simp only [piLaw_eval_expectation ν j, ← Finset.sum_mul, (piLaw μ).sum_one, one_mul]

variable {X Y : Type*} [Fintype X] [Fintype Y]
lemma relationMass_singleton_right (R : X → Y → Prop) (f : X → ℝ) (b : Y) :
    relationMass R f (uniformWeight {b}) = ∑ a∈Finset.univ.filter (fun a => R a b), f a := by
  rw [relationMass_by_target]
  simp [uniformWeight]

lemma relationMass_weighted_singleton (R : X → Y → Prop) (f : X → ℝ) (g : Y → ℝ) :
    (∑ b, g b*relationMass R f (uniformWeight {b})) = relationMass R f g := by
  simp_rw [relationMass_singleton_right R f]
  rw [relationMass_by_target R f g]

lemma relationMass_mixture_right {ι : Type*} [Fintype ι] (R : X → Y → Prop) (μ : Law ι)
    (f : X → ℝ) (g : ι → Y → ℝ) :
    (∑ i, μ i * relationMass R f (g i)) = relationMass R f (fun b => ∑ i, μ i*g i b) := by
  simp_rw [← relationMass_swap R f]
  exact relationMass_mixture_left (fun y x => R x y) μ g f

lemma originalLevelLaw_right_domination (μ : ∀ i, Law (A i)) (ν : ∀ j, Law (B j))
    (j : J) (R : X → Y → Prop) (S : B j → Finset Y) (g : X → ℝ) (q : Y → ℝ)
    (L : ℝ) (hg : ∀ a, 0≤g a)
    (hν : ∀ b, (∑ t, ν j t*uniformWeight (S t) b) ≤ L*q b) :
    (∑ z, originalLevelLaw μ ν z*relationMass R g (uniformWeight (S (z.2 j)))) ≤
      L*relationMass R g q := by
  rw [originalLevelLaw_second_mean μ ν j (fun t => relationMass R g (uniformWeight (S t))), relationMass_mixture_right]
  simp only [relationMass, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z _
  have h := mul_le_mul_of_nonneg_left (hν z.2) (hg z.1)
  rw [← Finset.mul_sum]
  nlinarith only [h]

lemma originalLevelLaw_left_domination (μ : ∀ i, Law (A i)) (ν : ∀ j, Law (B j))
    (i : I) (R : X → Y → Prop) (S : A i → Finset X) (p : X → ℝ) (g : Y → ℝ)
    (L : ℝ) (hg : ∀ b, 0≤g b)
    (hμ : ∀ a, (∑ t, μ i t*uniformWeight (S t) a) ≤ L*p a) :
    (∑ z, originalLevelLaw μ ν z*relationMass R (uniformWeight (S (z.1 i))) g) ≤
      L*relationMass R p g := by
  rw [originalLevelLaw_first_mean μ ν i (fun t => relationMass R (uniformWeight (S t)) g), relationMass_mixture_left]
  simp only [relationMass, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z _
  have h := mul_le_mul_of_nonneg_right (hμ z.1) (hg z.2)
  nlinarith only [h]
end SharpRamseyFive.FiniteEntropy

end OAI
