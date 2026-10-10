import OAI.NumberTheory.JointDickman.Arithmetic.RequiredPrimeSubset
import OAI.NumberTheory.JointDickman.Amplification.FiniteEventUnion
import OAI.NumberTheory.JointDickman.Amplification.ReciprocalTail
import Mathlib.Data.Nat.GCD.BigOperators

namespace OAI

/-!
# Removing GCD restrictions on two independent selected prime products

The probability of a common selected prime is bounded by the sum of the
products of the two marginal hit probabilities. For the independent
`1/(2p)` selection laws this is at most `1/(4N)` when all allowed primes
exceed `N`. The same bound controls any bounded test of the selected pair.
-/

namespace JointDickman

open Finset PublishedInputs

noncomputable def primeSubsetPairMass (P : Finset ℕ) (q r : ℕ → ℝ)
    (x : P.powerset × P.powerset) : ℝ :=
  bernoulliSubsetMass P q x.1.val * bernoulliSubsetMass P r x.2.val

theorem primeSubsetPairMass_nonneg (P : Finset ℕ) (q r : ℕ → ℝ)
    (hq : ∀ p ∈ P, 0 ≤ q p ∧ q p ≤ 1) (hr : ∀ p ∈ P, 0 ≤ r p ∧ r p ≤ 1)
    (x : P.powerset × P.powerset) : 0 ≤ primeSubsetPairMass P q r x :=
  mul_nonneg (bernoulliSubsetMass_nonneg (mem_powerset.mp x.1.property) hq)
    (bernoulliSubsetMass_nonneg (mem_powerset.mp x.2.property) hr)

open Classical in
theorem bernoulliSubsetMass_single_hit (P : Finset ℕ) (q : ℕ → ℝ) {p : ℕ} (hp : p ∈ P) :
    (∑ S : P.powerset, if p ∈ S.val then bernoulliSubsetMass P q S.val else 0) = q p := by
  rw [sum_coe_sort P.powerset (fun S => if p ∈ S then bernoulliSubsetMass P q S else 0)]
  simpa only [singleton_subset_iff, prod_singleton] using
    bernoulliSubsetMass_required P {p} q (singleton_subset_iff.mpr hp)

open Classical in
theorem primeSubsetPairMass_common_hit (P : Finset ℕ) (q r : ℕ → ℝ) {p : ℕ} (hp : p ∈ P) :
    finiteProbability (primeSubsetPairMass P q r) (fun x => p ∈ x.1.val ∧ p ∈ x.2.val) =
      q p * r p := by
  unfold finiteProbability
  rw [Fintype.sum_prod_type]
  have he (S T : P.powerset) :
      (@ite ℝ (p ∈ S.val ∧ p ∈ T.val) (Classical.propDecidable _)
        (primeSubsetPairMass P q r (S, T)) 0) =
      (if p ∈ S.val then bernoulliSubsetMass P q S.val else 0) *
        (if p ∈ T.val then bernoulliSubsetMass P r T.val else 0) := by
    by_cases hS : p ∈ S.val <;> by_cases hT : p ∈ T.val <;>
      simp [hS, hT, primeSubsetPairMass]
  simp_rw [he]
  rw [← sum_mul_sum, bernoulliSubsetMass_single_hit P q hp,
    bernoulliSubsetMass_single_hit P r hp]

theorem primeProducts_coprime_iff_disjoint {P A D : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hA : A ⊆ P) (hD : D ⊆ P) :
    (∏ p ∈ A, p).Coprime (∏ p ∈ D, p) ↔ Disjoint A D := by
  rw [Nat.coprime_prod_left_iff]
  simp_rw [Nat.coprime_prod_right_iff]
  constructor
  · intro h
    apply disjoint_left.mpr
    intro p hp hpd
    exact (Nat.coprime_primes (hP p (hA hp)) (hP p (hD hpd))).mp (h p hp p hpd) rfl
  · intro h p hp q hq
    apply (Nat.coprime_primes (hP p (hA hp)) (hP q (hD hq))).mpr
    intro heq
    subst q
    exact disjoint_left.mp h hp hq

open Classical in
/-- A genuine finite union bound for the failure of endpoint coprimality. -/
theorem primeSubsetPairMass_gcd_error (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (q r : ℕ → ℝ) (hq : ∀ p ∈ P, 0 ≤ q p ∧ q p ≤ 1)
    (hr : ∀ p ∈ P, 0 ≤ r p ∧ r p ≤ 1) :
    finiteProbability (primeSubsetPairMass P q r)
      (fun x => ¬(∏ p ∈ x.1.val, p).Coprime (∏ p ∈ x.2.val, p)) ≤
        ∑ p ∈ P, q p * r p := by
  have hw := primeSubsetPairMass_nonneg P q r hq hr
  calc
    _ ≤ finiteProbability (primeSubsetPairMass P q r)
        (fun x => ∃ p ∈ P, p ∈ x.1.val ∧ p ∈ x.2.val) := by
      apply finiteProbability_mono _ hw
      intro x hx
      have hd : ¬Disjoint x.1.val x.2.val := by
        simpa only [primeProducts_coprime_iff_disjoint hP
          (mem_powerset.mp x.1.property) (mem_powerset.mp x.2.property)] using hx
      obtain ⟨p, hp, hpd⟩ := not_disjoint_iff.mp hd
      exact ⟨p, mem_powerset.mp x.1.property hp, hp, hpd⟩
    _ ≤ ∑ p ∈ P, finiteProbability (primeSubsetPairMass P q r)
        (fun x => p ∈ x.1.val ∧ p ∈ x.2.val) :=
      finiteProbability_exists_mem _ hw P _
    _ = _ := sum_congr rfl (fun p hp => primeSubsetPairMass_common_hit P q r hp)

theorem halfPrimeSelection_bounds (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∀ p ∈ P, 0 ≤ (1 / 2 : ℝ) / p ∧ (1 / 2 : ℝ) / p ≤ 1 := by
  intro p hp
  have hp₀ : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
  have hp₂ : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
  refine ⟨by positivity, (div_le_one hp₀).mpr ?_⟩
  linarith

open Classical in
/-- The two independent selected products have the manuscript's `1/(2p)`
law. Their common-prime probability is at most `1/(4N)`. -/
theorem halfPrimeSubsetPair_gcd_error (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {N : ℕ} (hN : N ≠ 0) (hcut : ∀ p ∈ P, N < p) :
    finiteProbability (primeSubsetPairMass P (fun p => (1 / 2 : ℝ) / p)
      (fun p => (1 / 2 : ℝ) / p))
      (fun x => ¬(∏ p ∈ x.1.val, p).Coprime (∏ p ∈ x.2.val, p)) ≤ 1 / (4 * N : ℝ) := by
  have hb := primeSubsetPairMass_gcd_error P hP _ _
    (halfPrimeSelection_bounds P hP) (halfPrimeSelection_bounds P hP)
  refine hb.trans ?_
  have he (p : ℕ) : ((1 / 2 : ℝ) / p) * ((1 / 2 : ℝ) / p) = (1 / 4 : ℝ) * (1 / (p : ℝ) ^ 2) := by
    ring
  simp_rw [he]
  rw [← mul_sum]
  calc
    _ ≤ (1 / 4 : ℝ) * (1 / (N : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_reciprocal_square_tail P hN hcut) (by norm_num)
    _ = _ := by ring

open Classical in
/-- Inserting or removing endpoint coprimality in a bounded complex test
costs at most its bound times the common-prime probability. -/
theorem primeSubsetPair_coprime_test_error (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (q r : ℕ → ℝ) (hq : ∀ p ∈ P, 0 ≤ q p ∧ q p ≤ 1)
    (hr : ∀ p ∈ P, 0 ≤ r p ∧ r p ≤ 1)
    (F : P.powerset × P.powerset → ℂ) {L : ℝ} (hL : 0 ≤ L) (hF : ∀ x, ‖F x‖ ≤ L) :
    ‖(∑ x, (primeSubsetPairMass P q r x : ℂ) * F x) -
      (∑ x, if (∏ p ∈ x.1.val, p).Coprime (∏ p ∈ x.2.val, p) then
        (primeSubsetPairMass P q r x : ℂ) * F x else 0)‖ ≤ L * ∑ p ∈ P, q p * r p := by
  have hw := primeSubsetPairMass_nonneg P q r hq hr
  have he (x : P.powerset × P.powerset) :
      (primeSubsetPairMass P q r x : ℂ) * F x -
        (if (∏ p ∈ x.1.val, p).Coprime (∏ p ∈ x.2.val, p) then
          (primeSubsetPairMass P q r x : ℂ) * F x else 0) =
      if ¬(∏ p ∈ x.1.val, p).Coprime (∏ p ∈ x.2.val, p) then
        (primeSubsetPairMass P q r x : ℂ) * F x else 0 := by
    split_ifs <;> simp_all
  rw [← sum_sub_distrib]
  simp_rw [he]
  calc
    _ ≤ ∑ x, ‖if ¬(∏ p ∈ x.1.val, p).Coprime (∏ p ∈ x.2.val, p) then
        (primeSubsetPairMass P q r x : ℂ) * F x else 0‖ := norm_sum_le _ _
    _ ≤ L * finiteProbability (primeSubsetPairMass P q r)
        (fun x => ¬(∏ p ∈ x.1.val, p).Coprime (∏ p ∈ x.2.val, p)) := by
      unfold finiteProbability
      rw [mul_sum]
      apply sum_le_sum
      intro x _
      by_cases hc : (∏ p ∈ x.1.val, p).Coprime (∏ p ∈ x.2.val, p)
      · rw [ite_eq_right (not_not_intro hc), ite_eq_right (not_not_intro hc)]
        simp only [norm_zero, mul_zero, le_refl]
      · simp only [hc, not_false_eq_true, ite_true]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw x)]
        simpa only [mul_comm L] using mul_le_mul_of_nonneg_left (hF x) (hw x)
    _ ≤ _ := mul_le_mul_of_nonneg_left (primeSubsetPairMass_gcd_error P hP q r hq hr) hL

open Classical in
theorem halfPrimeSubsetPair_coprime_test_error (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {N : ℕ} (hN : N ≠ 0) (hcut : ∀ p ∈ P, N < p)
    (F : P.powerset × P.powerset → ℂ) {L : ℝ} (hL : 0 ≤ L) (hF : ∀ x, ‖F x‖ ≤ L) :
    ‖(∑ x, (primeSubsetPairMass P (fun p => (1 / 2 : ℝ) / p)
        (fun p => (1 / 2 : ℝ) / p) x : ℂ) * F x) -
      (∑ x, if (∏ p ∈ x.1.val, p).Coprime (∏ p ∈ x.2.val, p) then
        (primeSubsetPairMass P (fun p => (1 / 2 : ℝ) / p)
          (fun p => (1 / 2 : ℝ) / p) x : ℂ) * F x else 0)‖ ≤ L / (4 * N : ℝ) := by
  have hq := halfPrimeSelection_bounds P hP
  have h := primeSubsetPair_coprime_test_error P hP _ _ hq hq F hL hF
  refine h.trans ?_
  have hsum : (∑ p ∈ P, ((1 / 2 : ℝ) / p) * ((1 / 2 : ℝ) / p)) ≤ 1 / (4 * N : ℝ) := by
    simp_rw [show ∀ p : ℕ, ((1 / 2 : ℝ) / p) * ((1 / 2 : ℝ) / p) =
      (1 / 4 : ℝ) * (1 / (p : ℝ) ^ 2) from fun p => by ring]
    rw [← mul_sum]
    exact (mul_le_mul_of_nonneg_left (sum_reciprocal_square_tail P hN hcut)
      (by norm_num : (0 : ℝ) ≤ 1 / 4)).trans_eq (by ring)
  exact (mul_le_mul_of_nonneg_left hsum hL).trans_eq (by ring)

private theorem real_restriction_error_of_complex {Ω : Type*} [Fintype Ω]
    (w F : Ω → ℝ) (E : Ω → Prop) [DecidablePred E] {C : ℝ}
    (h : ‖(∑ x, (w x : ℂ) * (F x : ℂ)) -
      (∑ x, if E x then (w x : ℂ) * (F x : ℂ) else 0)‖ ≤ C) :
    |(∑ x, w x * F x) - (∑ x, if E x then w x * F x else 0)| ≤ C := by
  have hfull : (∑ x, (w x : ℂ) * (F x : ℂ)) = ((∑ x, w x * F x : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    apply sum_congr rfl
    intro x _
    exact (Complex.ofReal_mul _ _).symm
  have hrestricted : (∑ x, if E x then (w x : ℂ) * (F x : ℂ) else 0) =
    ((∑ x, if E x then w x * F x else 0 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    apply sum_congr rfl
    intro x _
    split_ifs
    · exact (Complex.ofReal_mul _ _).symm
    · rfl
  rw [hfull, hrestricted, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

open Classical in
/-- The same removal estimate for real arithmetic weights. -/
theorem halfPrimeSubsetPair_coprime_test_error_real (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {N : ℕ} (hN : N ≠ 0) (hcut : ∀ p ∈ P, N < p)
    (F : P.powerset × P.powerset → ℝ) {L : ℝ} (hL : 0 ≤ L) (hF : ∀ x, |F x| ≤ L) :
    |(∑ x, primeSubsetPairMass P (fun p => (1 / 2 : ℝ) / p)
        (fun p => (1 / 2 : ℝ) / p) x * F x) -
      (∑ x, if (∏ p ∈ x.1.val, p).Coprime (∏ p ∈ x.2.val, p) then
        primeSubsetPairMass P (fun p => (1 / 2 : ℝ) / p)
          (fun p => (1 / 2 : ℝ) / p) x * F x else 0)| ≤ L / (4 * N : ℝ) := by
  apply real_restriction_error_of_complex
  exact halfPrimeSubsetPair_coprime_test_error P hP hN hcut (fun x => (F x : ℂ)) hL
    (fun x => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hF x)

/-- If the two endpoints are coprime, the additive coefficient is coprime
to each endpoint as well. This does not require a restriction on the lag. -/
theorem additive_triple_coprime_iff {a b c j : ℕ} (heq : a = b + j * c) :
    a.Coprime b ∧ a.Coprime c ∧ b.Coprime c ↔ a.Coprime b := by
  constructor
  · exact And.left
  · intro hab
    have hba : b.Coprime (b + j * c) := by simpa only [← heq] using hab.symm
    have hbc : b.Coprime c :=
      (Nat.coprime_self_add_right.mp hba).coprime_dvd_right (dvd_mul_left c j)
    have hac : a.Coprime c := by
      rw [heq, Nat.coprime_add_mul_right_left]
      exact hbc
    exact ⟨hab, hac, hbc⟩

theorem additive_triple_coprime_iff_int_sub {a b c j : ℕ}
    (heq : (a : ℤ) - b = (j : ℤ) * c) :
    a.Coprime b ∧ a.Coprime c ∧ b.Coprime c ↔ a.Coprime b := by
  apply additive_triple_coprime_iff
  have h : (a : ℤ) = b + (j : ℤ) * c := by linarith
  exact_mod_cast h

end JointDickman

end OAI
