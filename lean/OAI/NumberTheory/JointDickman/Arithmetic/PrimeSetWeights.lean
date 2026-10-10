import OAI.NumberTheory.JointDickman.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace OAI

/-!
# Finite prime-selection and fair-split weights

The independent prime-set model and its fair splits satisfy exact finite
identities without prime asymptotics or analytic equidistribution premises.
-/

namespace JointDickman

open scoped BigOperators

/-- The independent-selection mass of a subset of `P`. All sums of these
masses below are restricted to `P.powerset`. -/
noncomputable def bernoulliSubsetMass {α : Type*} [DecidableEq α]
    (P : Finset α) (q : α → ℝ) (S : Finset α) : ℝ :=
  (∏ p ∈ S, q p) * ∏ p ∈ P \ S, (1 - q p)

theorem bernoulliSubsetMass_nonneg {α : Type*} [DecidableEq α]
    {P S : Finset α} {q : α → ℝ} (hS : S ⊆ P)
    (hq : ∀ p ∈ P, 0 ≤ q p ∧ q p ≤ 1) :
    0 ≤ bernoulliSubsetMass P q S := by
  apply mul_nonneg
  · exact Finset.prod_nonneg (fun p hp => (hq p (hS hp)).1)
  · exact Finset.prod_nonneg (fun p hp => sub_nonneg.mpr (hq p
      (Finset.mem_sdiff.mp hp).1).2)

theorem bernoulliSubsetMass_sum {α : Type*} [DecidableEq α]
    (P : Finset α) (q : α → ℝ) :
    ∑ S ∈ P.powerset, bernoulliSubsetMass P q S = 1 := by
  simp only [bernoulliSubsetMass]
  rw [← Finset.prod_add]
  simp

/-- The exact finite product formula for a multiplicative tilt. -/
theorem bernoulliSubsetMass_tilt {α : Type*} [DecidableEq α]
    (P : Finset α) (q v : α → ℝ) :
    ∑ S ∈ P.powerset, bernoulliSubsetMass P q S * (∏ p ∈ S, v p) =
      ∏ p ∈ P, (1 - q p + q p * v p) := by
  calc
    _ = ∑ S ∈ P.powerset,
        (∏ p ∈ S, q p * v p) * ∏ p ∈ P \ S, (1 - q p) := by
      apply Finset.sum_congr rfl
      intro S _
      rw [Finset.prod_mul_distrib]
      unfold bernoulliSubsetMass
      ring
    _ = _ := by rw [← Finset.prod_add]; congr 1; ext p; ring

theorem bernoulliSubsetMass_complement_formula {α : Type*} [DecidableEq α]
    {P S : Finset α} (q : α → ℝ) (hS : S ⊆ P)
    (hq : ∀ p ∈ P, 1 - q p ≠ 0) :
    bernoulliSubsetMass P q S =
      (∏ p ∈ P, (1 - q p)) * ∏ p ∈ S, (q p / (1 - q p)) := by
  have hne : (∏ p ∈ S, (1 - q p)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun p hp => hq p (hS hp))
  rw [Finset.prod_div_distrib]
  have hsplit := Finset.prod_sdiff hS (f := fun p => 1 - q p)
  rw [← hsplit]
  unfold bernoulliSubsetMass
  field_simp

/-- Products of distinct prime sets remember their set of factors. -/
theorem primeProduct_injective {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {S T : Finset ℕ} (hS : S ⊆ P) (hT : T ⊆ P)
    (heq : (∏ p ∈ S, p) = ∏ p ∈ T, p) : S = T := by
  have hSF := Nat.primeFactors_prod (fun p hp => hP p (hS hp))
  have hTF := Nat.primeFactors_prod (fun p hp => hP p (hT hp))
  rw [← hSF, ← hTF, heq]

/-- The prime-product pushforward of independent Bernoulli `z/p` selection;
this is the manuscript's `ν_z` on the finite allowed prime set. -/
noncomputable def primeProductMass (P : Finset ℕ) (z : ℝ) (n : ℕ) : ℝ :=
  ∑ S ∈ P.powerset, if (∏ p ∈ S, p) = n then
    bernoulliSubsetMass P (fun p => z / p) S else 0

theorem primeProductMass_at_product {P S : Finset ℕ} (z : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hS : S ⊆ P) :
    primeProductMass P z (∏ p ∈ S, p) =
      bernoulliSubsetMass P (fun p => z / p) S := by
  classical
  unfold primeProductMass
  rw [Finset.sum_eq_single S]
  · simp
  · intro T hT hTS
    have hne : (∏ p ∈ T, p) ≠ ∏ p ∈ S, p :=
      fun heq => hTS (primeProduct_injective hP (Finset.mem_powerset.mp hT) hS heq)
    simp [hne]
  · intro hn
    exact False.elim (hn (Finset.mem_powerset.mpr hS))

/-- Exact `ν_z` mass, factored into the all-absent probability and the
local odds ratios. -/
theorem primeProductMass_exact {P S : Finset ℕ} (z : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hS : S ⊆ P)
    (hz : ∀ p ∈ P, 1 - z / (p : ℝ) ≠ 0) :
    primeProductMass P z (∏ p ∈ S, p) =
      (∏ p ∈ P, (1 - z / (p : ℝ))) *
        ∏ p ∈ S, ((z / (p : ℝ)) / (1 - z / (p : ℝ))) := by
  rw [primeProductMass_at_product z hP hS]
  exact bernoulliSubsetMass_complement_formula _ hS hz

theorem primeProductMass_eq_zero {P : Finset ℕ} (z : ℝ) (n : ℕ)
    (hn : n ∉ P.powerset.image (fun S => ∏ p ∈ S, p)) :
    primeProductMass P z n = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro S hS
  have hne : (∏ p ∈ S, p) ≠ n := fun heq =>
    hn (Finset.mem_image.mpr ⟨S, hS, heq⟩)
  simp [hne]

/-- The pushforward mass is normalized on its finite set of prime products. -/
theorem primeProductMass_sum {P : Finset ℕ} (z : ℝ)
    (hP : ∀ p ∈ P, p.Prime) :
    ∑ n ∈ P.powerset.image (fun S => ∏ p ∈ S, p), primeProductMass P z n = 1 := by
  classical
  rw [Finset.sum_image]
  · calc
      _ = ∑ S ∈ P.powerset, bernoulliSubsetMass P (fun p => z / (p : ℝ)) S := by
        apply Finset.sum_congr rfl
        intro S hS
        exact primeProductMass_at_product z hP (Finset.mem_powerset.mp hS)
      _ = 1 := bernoulliSubsetMass_sum P _
  · intro S hS T hT heq
    exact primeProduct_injective hP (Finset.mem_powerset.mp hS)
      (Finset.mem_powerset.mp hT) heq

/-- Probability `1/2` at each member of a fixed site gives the uniform
fair-split mass, including the empty site. -/
theorem bernoulliSubsetMass_half {α : Type*} [DecidableEq α]
    {S T : Finset α} (hT : T ⊆ S) :
    bernoulliSubsetMass S (fun _ => (1 / 2 : ℝ)) T = (1 / 2 : ℝ) ^ S.card := by
  unfold bernoulliSubsetMass
  simp only [Finset.prod_const]
  norm_num only [show 1 - (1 / 2 : ℝ) = 1 / 2 by norm_num]
  rw [← pow_add, add_comm T.card, Finset.card_sdiff_add_card_eq_card hT]

/-- The coefficient and remaining-site weight convert a sum over divisors
into a fair-split expectation, with total normalization `L * R`. -/
theorem fairSplit_weight_identity {α : Type*} [DecidableEq α]
    {S T : Finset α} (hT : T ⊆ S) (L R : ℝ) (hR : 0 ≤ R) :
    (L * Real.sqrt R * (1 / 2 : ℝ) ^ T.card) *
        (Real.sqrt R * (1 / 2 : ℝ) ^ (S \ T).card) =
      L * R * (1 / 2 : ℝ) ^ S.card := by
  calc
    _ = L * (Real.sqrt R * Real.sqrt R) *
        ((1 / 2 : ℝ) ^ T.card * (1 / 2 : ℝ) ^ (S \ T).card) := by ring
    _ = _ := by
      rw [Real.mul_self_sqrt hR, ← pow_add, add_comm T.card,
        Finset.card_sdiff_add_card_eq_card hT]

/-- A finite positive-tilt Markov bound, before any prime-sum estimate. -/
theorem bernoulliSubsetMass_tilt_tail {α : Type*} [DecidableEq α]
    (P : Finset α) (q v : α → ℝ) (r : ℝ)
    (hq : ∀ p ∈ P, 0 ≤ q p ∧ q p ≤ 1)
    (hv : ∀ p ∈ P, 0 ≤ v p) :
    r * (∑ S ∈ P.powerset, if r ≤ ∏ p ∈ S, v p then
      bernoulliSubsetMass P q S else 0) ≤
      ∏ p ∈ P, (1 - q p + q p * v p) := by
  classical
  rw [← bernoulliSubsetMass_tilt, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro S hS
  have hSP := Finset.mem_powerset.mp hS
  have hmass := bernoulliSubsetMass_nonneg hSP hq
  split_ifs with h
  · nlinarith
  · simpa using mul_nonneg hmass (Finset.prod_nonneg (fun p hp => hv p (hSP hp)))

/-- Exact exponential moment of the number of selected primes. -/
theorem bernoulliSubsetMass_count_exp {α : Type*} [DecidableEq α]
    (P : Finset α) (q : α → ℝ) (t : ℝ) :
    ∑ S ∈ P.powerset, bernoulliSubsetMass P q S * Real.exp (t * S.card) =
      ∏ p ∈ P, (1 - q p + q p * Real.exp t) := by
  have hprod (S : Finset α) : (∏ _p ∈ S, Real.exp t) = Real.exp (t * S.card) := by
    rw [Finset.prod_const, ← Real.exp_nat_mul]
    congr 1
    ring
  simpa only [hprod] using bernoulliSubsetMass_tilt P q (fun _ => Real.exp t)

/-- Exponential upper tail for the selected-prime count. Prime estimates
are needed only afterward to bound the explicit product on the right. -/
theorem bernoulliSubsetMass_count_tail {α : Type*} [DecidableEq α]
    (P : Finset α) (q : α → ℝ) (k : ℕ) {t : ℝ} (ht : 0 ≤ t)
    (hq : ∀ p ∈ P, 0 ≤ q p ∧ q p ≤ 1) :
    (∑ S ∈ P.powerset, if k ≤ S.card then bernoulliSubsetMass P q S else 0) ≤
      Real.exp (-t * k) * ∏ p ∈ P, (1 - q p + q p * Real.exp t) := by
  classical
  have hbound : Real.exp (t * k) *
      (∑ S ∈ P.powerset, if k ≤ S.card then bernoulliSubsetMass P q S else 0) ≤
      ∏ p ∈ P, (1 - q p + q p * Real.exp t) := by
    rw [← bernoulliSubsetMass_count_exp, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro S hS
    have hmass := bernoulliSubsetMass_nonneg (Finset.mem_powerset.mp hS) hq
    split_ifs with h
    · have hcast : (k : ℝ) ≤ S.card := by exact_mod_cast h
      have hexp := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hcast ht)
      nlinarith
    · simpa using mul_nonneg hmass (Real.exp_pos _).le
  have hmul := mul_le_mul_of_nonneg_left hbound (Real.exp_pos (-t * k)).le
  have he : Real.exp (-t * k) * Real.exp (t * k) = 1 := by
    rw [← Real.exp_add]
    rw [show -t * (k : ℝ) + t * k = 0 by ring, Real.exp_zero]
  simpa only [← mul_assoc, he, one_mul] using hmul

end JointDickman

end OAI
