import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

namespace OAI

/-!
# Collision energy and occupied residue classes

The collision-to-occupancy argument is used in §6 of *A Low-Space Algorithm
for Worst-Case Subset Sum*. Its published antecedents are Austrin, Kaski,
Koivisto and Nederlof, *Dense Subset Sum May Be the Hardest*, STACS 2016,
Proposition 3.5, and Nederlof and Węgrzycki, *Improving Schroeppel and Shamir's
Algorithm for Subset Sum via Orthogonal Vectors*, arXiv:2010.08576v2,
Lemma 3.2, especially equation (1) and the following Cauchy–Schwarz argument.

Those published statements assume exponentially bounded integer weights.
The finite collision-to-occupancy bound instead takes the collision estimate
as an explicit hypothesis. The manuscript's prime-factor estimate supplies
that hypothesis for polynomial-bit inputs.
-/

namespace LowSpaceSubsetSum

open scoped BigOperators

variable {α β Ω : Type*} [DecidableEq β]

/-- The multiplicity of one image value, counting the distinct elements of `X`. -/
def fiberSize (X : Finset α) (f : α → β) (b : β) : ℕ :=
  (X.filter fun x => f x = b).card

/-- The sum of squared residue-class sizes. -/
def collisionEnergy (X : Finset α) (f : α → β) : ℕ :=
  ∑ b ∈ X.image f, fiberSize X f b ^ 2

/-- Ordered collisions include diagonal pairs. -/
def collisionPairs (X : Finset α) (f : α → β) : Finset (α × α) :=
  (X ×ˢ X).filter fun p => f p.1 = f p.2

theorem sum_fiberSize (X : Finset α) (f : α → β) :
    (∑ b ∈ X.image f, fiberSize X f b) = X.card := by
  exact (Finset.card_eq_sum_card_fiberwise fun x hx => Finset.mem_image_of_mem f hx).symm

/-- The deterministic Cauchy–Schwarz step: a small collision energy forces
many distinct occupied residue classes. -/
theorem card_sq_le_occupied_mul_energy (X : Finset α) (f : α → β) :
    X.card ^ 2 ≤ (X.image f).card * collisionEnergy X f := by
  have hcs := sq_sum_le_card_mul_sum_sq (s := X.image f)
    (f := fun b => (fiberSize X f b : ℝ))
  have hsum : (∑ b ∈ X.image f, (fiberSize X f b : ℝ)) = (X.card : ℝ) := by
    exact_mod_cast sum_fiberSize X f
  rw [hsum] at hcs
  exact_mod_cast hcs

theorem collisionEnergy_eq_card_pairs (X : Finset α) (f : α → β) :
    collisionEnergy X f = (collisionPairs X f).card := by
  have hfiber (b : β) :
      (collisionPairs X f).filter (fun p => f p.1 = b) =
        (X.filter fun x => f x = b) ×ˢ (X.filter fun x => f x = b) := by
    ext p
    simp only [collisionPairs, Finset.mem_filter, Finset.mem_product]
    aesop
  have hmaps : ∀ p ∈ collisionPairs X f, f p.1 ∈ X.image f := by
    intro p hp
    exact Finset.mem_image_of_mem f (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro b _
  rw [hfiber, Finset.card_product]
  simp [fiberSize, pow_two]

theorem collisionEnergy_eq_sum_pairs (X : Finset α) (f : α → β) :
    (collisionEnergy X f : ℝ) =
      ∑ x ∈ X, ∑ y ∈ X, if f x = f y then (1 : ℝ) else 0 := by
  rw [collisionEnergy_eq_card_pairs]
  rw [Finset.card_eq_sum_ones]
  simp only [collisionPairs, Nat.cast_sum, Finset.sum_filter,
    Finset.sum_product, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

/-- A pointwise collision-energy bound gives a quantitative occupied-class
bound. The statement uses real cardinalities to avoid integer rounding. -/
theorem occupied_ge_of_energy_le (X : Finset α) (f : α → β)
    {T : ℝ} (hT : 0 < T) (henergy : (collisionEnergy X f : ℝ) ≤ T) :
    (X.card : ℝ) ^ 2 / T ≤ (X.image f).card := by
  apply (div_le_iff₀ hT).mpr
  have hc : (X.card : ℝ) ^ 2 ≤
      ((X.image f).card : ℝ) * (collisionEnergy X f : ℝ) := by
    exact_mod_cast card_sq_le_occupied_mul_energy X f
  exact hc.trans (mul_le_mul_of_nonneg_left henergy (Nat.cast_nonneg _))

/-- The smallest probabilistic interface needed from a random modulus:
every distinct pair has collision probability at most `δ`. The weights
`prob` form a finite probability distribution on `seeds`. -/
def PairwiseCollisionBound (seeds : Finset Ω) (prob : Ω → ℝ)
    (X : Finset α) (hash : Ω → α → β) (δ : ℝ) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, x ≠ y →
    (∑ ω ∈ seeds, prob ω * if hash ω x = hash ω y then (1 : ℝ) else 0) ≤ δ

/-- The published collision-energy calculation, for an arbitrary finite
sampling law and with its exact collision bound exposed as a hypothesis. -/
theorem expected_energy_le (seeds : Finset Ω) (prob : Ω → ℝ)
    (X : Finset α) (hash : Ω → α → β) {δ : ℝ}
    (hprob : ∑ ω ∈ seeds, prob ω = 1) (hδ : 0 ≤ δ)
    (hcollision : PairwiseCollisionBound seeds prob X hash δ) :
    (∑ ω ∈ seeds, prob ω * (collisionEnergy X (hash ω) : ℝ)) ≤
      X.card + δ * (X.card : ℝ) ^ 2 := by
  classical
  have hswap :
      (∑ ω ∈ seeds, prob ω * (collisionEnergy X (hash ω) : ℝ)) =
        ∑ x ∈ X, ∑ y ∈ X,
          ∑ ω ∈ seeds, prob ω * if hash ω x = hash ω y then (1 : ℝ) else 0 := by
    simp_rw [collisionEnergy_eq_sum_pairs, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_comm]
  rw [hswap]
  calc
    _ ≤ ∑ x ∈ X, ∑ y ∈ X, ((if x = y then (1 : ℝ) else 0) + δ) := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro y hy
      by_cases hxy : x = y
      · subst y
        simpa [hprob] using hδ
      · simpa [hxy] using hcollision x hx y hy hxy
    _ = X.card + δ * (X.card : ℝ) ^ 2 := by
      simp only [Finset.sum_add_distrib]
      simp [pow_two, mul_comm, mul_left_comm]

/-- A finite-law Markov bound, retaining precisely the good event needed
for the occupancy argument. -/
theorem probability_energy_le (seeds : Finset Ω) (prob : Ω → ℝ)
    (X : Finset α) (hash : Ω → α → β)
    (hnonneg : ∀ ω ∈ seeds, 0 ≤ prob ω)
    (hprob : ∑ ω ∈ seeds, prob ω = 1)
    {M T : ℝ} (hT : 0 < T)
    (hmean : (∑ ω ∈ seeds, prob ω * (collisionEnergy X (hash ω) : ℝ)) ≤ M) :
    1 - M / T ≤
      ∑ ω ∈ seeds.filter (fun ω => (collisionEnergy X (hash ω) : ℝ) ≤ T), prob ω := by
  classical
  let bad := seeds.filter (fun ω => T < (collisionEnergy X (hash ω) : ℝ))
  have hbad : T * (∑ ω ∈ bad, prob ω) ≤ M := by
    calc
      _ = ∑ ω ∈ bad, prob ω * T := by rw [Finset.mul_sum]; simp [mul_comm]
      _ ≤ ∑ ω ∈ bad, prob ω * (collisionEnergy X (hash ω) : ℝ) := by
        apply Finset.sum_le_sum
        intro ω hω
        have hmem := Finset.mem_filter.mp hω
        exact mul_le_mul_of_nonneg_left hmem.2.le (hnonneg ω hmem.1)
      _ ≤ ∑ ω ∈ seeds, prob ω * (collisionEnergy X (hash ω) : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro ω hω _
        exact mul_nonneg (hnonneg ω hω) (Nat.cast_nonneg _)
      _ ≤ M := hmean
  have hbad' : (∑ ω ∈ bad, prob ω) ≤ M / T := by
    apply (le_div_iff₀ hT).mpr
    simpa [mul_comm] using hbad
  have hpartition :
      (∑ ω ∈ seeds.filter (fun ω => (collisionEnergy X (hash ω) : ℝ) ≤ T), prob ω) +
        (∑ ω ∈ bad, prob ω) = 1 := by
    simp only [bad, Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    convert hprob using 1
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hω : (collisionEnergy X (hash ω) : ℝ) ≤ T
    · simp [hω, not_lt_of_ge hω]
    · simp [hω, lt_of_not_ge hω]
  linarith

/-- Collision bounds imply a lower bound on the probability of many occupied
classes. This includes the Markov and Cauchy–Schwarz steps, rather than
assuming the desired occupancy conclusion. -/
theorem occupied_probability_of_collision_bound
    (seeds : Finset Ω) (prob : Ω → ℝ)
    (X : Finset α) (hash : Ω → α → β)
    (hnonneg : ∀ ω ∈ seeds, 0 ≤ prob ω)
    (hprob : ∑ ω ∈ seeds, prob ω = 1)
    {δ T : ℝ} (hδ : 0 ≤ δ) (hT : 0 < T)
    (hcollision : PairwiseCollisionBound seeds prob X hash δ) :
    1 - ((X.card : ℝ) + δ * (X.card : ℝ) ^ 2) / T ≤
      ∑ ω ∈ seeds.filter
        (fun ω => (X.card : ℝ) ^ 2 / T ≤ ((X.image (hash ω)).card : ℝ)), prob ω := by
  classical
  have hmarkov := probability_energy_le seeds prob X hash hnonneg hprob hT
    (expected_energy_le seeds prob X hash hprob hδ hcollision)
  apply hmarkov.trans
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ω hω
    have hmem := Finset.mem_filter.mp hω
    exact Finset.mem_filter.mpr ⟨hmem.1, occupied_ge_of_energy_le X (hash ω) hT hmem.2⟩
  · intro ω hω _
    exact hnonneg ω (Finset.mem_filter.mp hω).1

end LowSpaceSubsetSum

end OAI
