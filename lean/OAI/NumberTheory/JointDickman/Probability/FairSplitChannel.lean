import OAI.NumberTheory.JointDickman.Probability.TwoSplitLaw
import OAI.NumberTheory.JointDickman.Probability.FiniteChannels

namespace OAI

/-!
# The actual finite fair-split channel

A site is a vector of independent Bernoulli bits. Conditional on that site,
each present prime is retained independently with probability one half and
each absent prime stays absent. Integrating two conditionally independent
retentions gives exactly the same-site two-split law, including for arbitrary
output cells. This connects that law to the actual finite channel kernel.
-/

namespace JointDickman

open scoped BigOperators

/-- One conditional retention bit. -/
noncomputable def fairRetentionBitMass (hit retained : Bool) : ℝ :=
  if hit then bernoulliBitMass (1 / 2) retained else if retained then 0 else 1

theorem fairRetentionBitMass_nonneg (hit retained : Bool) :
    0 ≤ fairRetentionBitMass hit retained := by
  cases hit <;> cases retained <;> norm_num [fairRetentionBitMass, bernoulliBitMass]

theorem fairRetentionBitMass_sum (hit : Bool) : ∑ retained, fairRetentionBitMass hit retained = 1 := by
  cases hit <;> norm_num [fairRetentionBitMass, bernoulliBitMass, Fintype.sum_bool]

/-- This is the conditional independence in the definition of two fair splits. -/
theorem conditionalFairSplitMass_factor (hit b c : Bool) :
    conditionalFairSplitMass hit (b, c) =
      fairRetentionBitMass hit b * fairRetentionBitMass hit c := by
  cases hit <;> cases b <;> cases c <;>
    norm_num [conditionalFairSplitMass, fairRetentionBitMass, bernoulliBitMass]

theorem fairRetentionBitMass_marginal (q : ℝ) (b : Bool) :
    (∑ hit, bernoulliBitMass q hit * fairRetentionBitMass hit b) = bernoulliBitMass (q / 2) b := by
  cases b <;> simp [fairRetentionBitMass, bernoulliBitMass] <;> ring

/-- Independent Bernoulli mass of the original site. -/
noncomputable def bernoulliSiteMass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (x : ι → Bool) : ℝ := finiteProductMass (fun i => bernoulliBitMass (q i)) x

/-- Conditional probability of a particular retained subset of a site. -/
noncomputable def fairRetentionMass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x y : ι → Bool) : ℝ := finiteProductMass (fun i => fairRetentionBitMass (x i)) y

theorem fairRetentionMass_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x y : ι → Bool) : 0 ≤ fairRetentionMass x y :=
  finiteProductMass_nonneg _ (fun i => fairRetentionBitMass_nonneg (x i)) y

theorem fairRetentionMass_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → Bool) : ∑ y, fairRetentionMass x y = 1 :=
  finiteProductMass_sum _ (fun i => fairRetentionBitMass_sum (x i))

theorem bernoulliSiteMass_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) : ∑ x, bernoulliSiteMass q x = 1 :=
  finiteProductMass_sum _ (fun i => bernoulliBitMass_sum (q i))

theorem bernoulliSiteMass_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (x : ι → Bool) :
    0 ≤ bernoulliSiteMass q x :=
  finiteProductMass_nonneg _ (fun i => bernoulliBitMass_nonneg (hq i)) x

/-- Summing out the shared site gives the actual joint retention law. -/
theorem fairRetentionMass_joint {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (y z : ι → Bool) :
    (∑ x, bernoulliSiteMass q x * fairRetentionMass x y * fairRetentionMass x z) =
      sameSiteTwoSplitProductMass q (fun i => (y i, z i)) := by
  classical
  have hp (x : ι → Bool) :
      bernoulliSiteMass q x * fairRetentionMass x y * fairRetentionMass x z =
        ∏ i, bernoulliBitMass (q i) (x i) * fairRetentionBitMass (x i) (y i) *
          fairRetentionBitMass (x i) (z i) := by
    simp only [bernoulliSiteMass, fairRetentionMass, finiteProductMass, Finset.prod_mul_distrib]
  simp_rw [hp]
  rw [← Fintype.prod_sum (fun i hit => bernoulliBitMass (q i) hit *
    fairRetentionBitMass hit (y i) * fairRetentionBitMass hit (z i))]
  unfold sameSiteTwoSplitProductMass finiteProductMass
  apply Finset.prod_congr rfl
  intro i _
  unfold sameSiteTwoSplitMass
  apply Finset.sum_congr rfl
  intro hit _
  rw [conditionalFairSplitMass_factor]
  ring

theorem fairRetentionMass_marginal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (y : ι → Bool) :
    (∑ x, bernoulliSiteMass q x * fairRetentionMass x y) =
      bernoulliSiteMass (fun i => q i / 2) y := by
  classical
  simp only [bernoulliSiteMass, fairRetentionMass, finiteProductMass, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i hit => bernoulliBitMass (q i) hit *
    fairRetentionBitMass hit (y i))]
  simp_rw [fairRetentionBitMass_marginal]

/-- Conditional expectation of a test of the retained subset. -/
noncomputable def fairSplitAverage {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → Bool) (f : (ι → Bool) → ℝ) : ℝ := ∑ y, fairRetentionMass x y * f y

theorem fairSplitAverage_bilinear {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (f g : (ι → Bool) → ℝ) :
    (∑ x, bernoulliSiteMass q x * fairSplitAverage x f * fairSplitAverage x g) =
      ∑ z, sameSiteTwoSplitProductMass q z * f (fun i => (z i).1) * g (fun i => (z i).2) := by
  classical
  calc
    _ = ∑ z, ∑ y, (∑ x, bernoulliSiteMass q x * fairRetentionMass x y * fairRetentionMass x z) *
        f y * g z := by
      unfold fairSplitAverage
      simp only [mul_assoc]
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = ∑ z, ∑ y, sameSiteTwoSplitProductMass q (fun i => (y i, z i)) * f y * g z := by
      simp_rw [fairRetentionMass_joint]
    _ = ∑ y, ∑ z, sameSiteTwoSplitProductMass q (fun i => (y i, z i)) * f y * g z :=
      Finset.sum_comm
    _ = ∑ yz : (ι → Bool) × (ι → Bool),
        sameSiteTwoSplitProductMass q (fun i => (yz.1 i, yz.2 i)) * f yz.1 * g yz.2 :=
      (Fintype.sum_prod_type (fun yz : (ι → Bool) × (ι → Bool) =>
        sameSiteTwoSplitProductMass q (fun i => (yz.1 i, yz.2 i)) * f yz.1 * g yz.2)).symm
    _ = _ := ((Equiv.arrowProdEquivProdArrow ι (fun _ => Bool) (fun _ => Bool)).sum_comp
      (fun yz => sameSiteTwoSplitProductMass q (fun i => (yz.1 i, yz.2 i)) * f yz.1 * g yz.2)).symm

theorem fairSplitAverage_marginal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (f : (ι → Bool) → ℝ) :
    (∑ x, bernoulliSiteMass q x * fairSplitAverage x f) =
      ∑ y, bernoulliSiteMass (fun i => q i / 2) y * f y := by
  classical
  unfold fairSplitAverage
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  simp only [← mul_assoc]
  rw [← Finset.sum_mul, fairRetentionMass_marginal]

/-- Actual transition probability to an output cell of the retained subset. -/
noncomputable def fairSplitTransition {ι A : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq A]
    (cell : (ι → Bool) → A) (x : ι → Bool) (a : A) : ℝ := by
  classical
  exact ∑ y, if cell y = a then fairRetentionMass x y else 0

theorem fairSplitTransition_eq_average {ι A : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq A]
    (cell : (ι → Bool) → A) (x : ι → Bool) (a : A) :
    fairSplitTransition cell x a = fairSplitAverage x (fun y => if cell y = a then 1 else 0) := by
  classical
  unfold fairSplitTransition fairSplitAverage
  apply Finset.sum_congr rfl
  intro y _
  split_ifs <;> simp_all

theorem fairSplitTransition_twoSplit_mass {ι A : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq A]
    (q : ι → ℝ) (cell : (ι → Bool) → A) (a b : A) :
    (∑ x, bernoulliSiteMass q x * fairSplitTransition cell x a * fairSplitTransition cell x b) =
      ∑ z, if cell (fun i => (z i).1) = a ∧ cell (fun i => (z i).2) = b then
        sameSiteTwoSplitProductMass q z else 0 := by
  classical
  simp_rw [fairSplitTransition_eq_average]
  rw [fairSplitAverage_bilinear]
  apply Finset.sum_congr rfl
  intro z _
  by_cases ha : cell (fun i => (z i).1) = a <;>
    by_cases hb : cell (fun i => (z i).2) = b <;> simp [ha, hb]

/-- Consequently the actual finite channel's two-split kernel is the cell
mass of the explicit two-split law divided by the two output atom weights. -/
theorem fairSplitTransition_twoSplitKernel {ι A : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq A]
    (q : ι → ℝ) (cell : (ι → Bool) → A) (μ : A → ℝ) (a b : A) :
    finiteTwoSplitKernel (bernoulliSiteMass q) μ (fairSplitTransition cell) a b =
      (∑ z, if cell (fun i => (z i).1) = a ∧ cell (fun i => (z i).2) = b then
        sameSiteTwoSplitProductMass q z else 0) / (μ a * μ b) := by
  unfold finiteTwoSplitKernel
  rw [fairSplitTransition_twoSplit_mass]

/-- Prime product of one retained bit vector. -/
noncomputable def retainedPrimeProduct (Q : Finset ℕ) (y : Q → Bool) : ℕ :=
  ∏ p, if y p then p.val else 1

theorem actualSplitProducts_eq_retained (Q : Finset ℕ) (z : Q → Bool × Bool) :
    actualSplitProducts Q z =
      (retainedPrimeProduct Q (fun p => (z p).1), retainedPrimeProduct Q (fun p => (z p).2)) := rfl

/-- The conditional probability `p_A(S)` that a fair split of the site
has its retained prime product in the specified cell. -/
noncomputable def fairSplitPrimeCell (Q : Finset ℕ) (A : Set ℕ) (x : Q → Bool) : ℝ := by
  classical
  exact fairSplitAverage x (fun y => if retainedPrimeProduct Q y ∈ A then 1 else 0)

open Classical in
theorem fairSplitPrimeCell_eq (Q : Finset ℕ) (A : Set ℕ) (x : Q → Bool) :
    fairSplitPrimeCell Q A x =
      ∑ y, if retainedPrimeProduct Q y ∈ A then fairRetentionMass x y else 0 := by
  unfold fairSplitPrimeCell fairSplitAverage
  apply Finset.sum_congr rfl
  intro y _
  split_ifs <;> simp_all

open Classical in
/-- The actual fair-split channel numerator equals the cell mass of the
two-split prime-product law. The equality holds for any site probabilities. -/
theorem fairSplitPrimeCell_joint (Q : Finset ℕ) (q : Q → ℝ) (A B : Set ℕ) :
    (∑ x, bernoulliSiteMass q x * fairSplitPrimeCell Q A x * fairSplitPrimeCell Q B x) =
      ∑ z, if (actualSplitProducts Q z).1 ∈ A ∧ (actualSplitProducts Q z).2 ∈ B then
        sameSiteTwoSplitProductMass q z else 0 := by
  unfold fairSplitPrimeCell
  rw [fairSplitAverage_bilinear]
  apply Finset.sum_congr rfl
  intro z _
  rw [actualSplitProducts_eq_retained]
  by_cases ha : retainedPrimeProduct Q (fun p => (z p).1) ∈ A <;>
    by_cases hb : retainedPrimeProduct Q (fun p => (z p).2) ∈ B <;> simp [ha, hb]

open Classical in
/-- A single fair split changes the prime-site probabilities from `1/p`
to `1/(2p)`, exactly and before any prime asymptotics. -/
theorem fairSplitPrimeCell_marginal (Q : Finset ℕ) (A : Set ℕ) :
    (∑ x, bernoulliSiteMass (fun p : Q => 1 / (p.val : ℝ)) x * fairSplitPrimeCell Q A x) =
      ∑ y, if retainedPrimeProduct Q y ∈ A then
        bernoulliSiteMass (fun p : Q => 1 / (2 * (p.val : ℝ))) y else 0 := by
  unfold fairSplitPrimeCell
  rw [fairSplitAverage_marginal]
  have hq : (fun p : Q => (1 / (p.val : ℝ)) / 2) = (fun p : Q => 1 / (2 * (p.val : ℝ))) := by
    funext p
    rw [div_div, mul_comm (p.val : ℝ) 2]
  rw [hq]
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : retainedPrimeProduct Q y ∈ A <;> simp [h]

open Classical in
/-- Kernel identity for any finite partition of the retained prime product.
This is the direct bridge from the actual channel to two-split cell estimates. -/
theorem fairPrimeTransition_twoSplitKernel {A : Type*} [DecidableEq A]
    (Q : Finset ℕ) (q : Q → ℝ) (cell : ℕ → A) (μ : A → ℝ) (a b : A) :
    finiteTwoSplitKernel (bernoulliSiteMass q) μ
      (fairSplitTransition (fun y => cell (retainedPrimeProduct Q y))) a b =
      (∑ z, if cell (actualSplitProducts Q z).1 = a ∧ cell (actualSplitProducts Q z).2 = b then
        sameSiteTwoSplitProductMass q z else 0) / (μ a * μ b) := by
  rw [fairSplitTransition_twoSplitKernel]
  rfl

end JointDickman

end OAI
