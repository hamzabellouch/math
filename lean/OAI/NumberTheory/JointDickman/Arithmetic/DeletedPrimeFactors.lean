import OAI.NumberTheory.JointDickman.Amplification.ThreeFormLocalBound
import OAI.NumberTheory.JointDickman.Amplification.SingularFactor
import OAI.NumberTheory.JointDickman.Arithmetic.SelectedPrimeOdds
import OAI.NumberTheory.JointDickman.Amplification.AuxiliaryScale

namespace OAI

/-! # The cost of deleting exceptional primes from a two-form sieve -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem inverse_square_le_singular {p : ℕ} (hp : p.Prime) {d : ℝ}
    (hd : 0 ≤ d) (hd1 : d ≤ 1) :
    ((1 - d / p)⁻¹) ^ 2 ≤ 1 + 24 / (p : ℝ) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hx : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
  have hs0 : 0 < 1 - d / (p : ℝ) := by
    have : d / (p : ℝ) ≤ 1 / 2 := (div_le_iff₀ hp0).mpr (by linarith)
    linarith
  have hs1 : 1 - d / (p : ℝ) ≤ 1 := sub_le_self _ (div_nonneg hd hp0.le)
  have hcube : 1 ≤ (1 - d / (p : ℝ)) ^ 3 * (1 + 24 / (p : ℝ)) := by
    simpa only [div_eq_mul_inv, one_mul] using
      one_le_cube_singular_factor (by positivity : (0 : ℝ) ≤ 1 / p) hx hd hd1
  have hsquare : (1 - d / (p : ℝ)) ^ 3 ≤ (1 - d / (p : ℝ)) ^ 2 := by
    exact pow_le_pow_of_le_one hs0.le hs1 (by norm_num)
  have hsq : 1 ≤ (1 - d / (p : ℝ)) ^ 2 * (1 + 24 / (p : ℝ)) :=
    hcube.trans (mul_le_mul_of_nonneg_right hsquare (by positivity))
  rw [inv_pow]
  exact (inv_le_iff_one_le_mul₀ (sq_pos_of_pos hs0)).mpr (by simpa only [mul_comm] using hsq)

open Classical in
theorem delete_two_prime_sets (P : Finset ℕ) (a b : ℕ → Prop) (f : ℕ → ℝ)
    (hf : ∀ p ∈ P, 0 < f p ∧ f p ≤ 1) :
    (∏ p ∈ P.filter (fun p => ¬a p ∧ ¬b p), f p) ^ 2 ≤
      (∏ p ∈ P, f p) ^ 2 * (∏ p ∈ P.filter a, (f p)⁻¹) ^ 2 *
        (∏ p ∈ P.filter b, (f p)⁻¹) ^ 2 := by
  rw [← prod_pow, prod_filter]
  have hlocal (p : ℕ) (hp : p ∈ P) :
      (if ¬a p ∧ ¬b p then f p ^ 2 else 1) ≤
        f p ^ 2 * (if a p then (f p)⁻¹ ^ 2 else 1) * (if b p then (f p)⁻¹ ^ 2 else 1) := by
    have heq : f p ^ 2 * (f p)⁻¹ ^ 2 = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ (hf p hp).1.ne', one_pow]
    have hinv : 1 ≤ (f p)⁻¹ ^ 2 := one_le_pow₀ ((one_le_inv₀ (hf p hp).1).mpr (hf p hp).2)
    by_cases ha : a p <;> by_cases hb : b p <;>
      simp only [ha, hb, not_true_eq_false, not_false_eq_true, and_self, and_false,
        false_and, ite_true, ite_false, mul_one, heq, one_mul] <;>
      first | exact hinv | exact le_rfl
  calc
    _ ≤ ∏ p ∈ P, f p ^ 2 * (if a p then (f p)⁻¹ ^ 2 else 1) *
        (if b p then (f p)⁻¹ ^ 2 else 1) := by
      apply prod_le_prod₀
      · intro p _
        split_ifs <;> positivity
      · exact hlocal
    _ = _ := by
      simp only [prod_mul_distrib, ← prod_pow, ← prod_filter]

open Classical in
theorem deleted_divisor_factor_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (d : ℕ → ℝ) (hd : ∀ p ∈ P, 0 ≤ d p ∧ d p ≤ 1) {j : ℕ} (hj : j ≠ 0) :
    (∏ p ∈ P.filter (fun p => p ∣ j), (1 - d p / p)⁻¹) ^ 2 ≤ singularFactor 24 j := by
  rw [← prod_pow]
  calc
    _ ≤ ∏ p ∈ P.filter (fun p => p ∣ j), (1 + 24 / (p : ℝ)) := by
      apply prod_le_prod₀ (fun _ _ => sq_nonneg _)
      intro p hp
      exact inverse_square_le_singular (hP p (mem_filter.mp hp).1)
        (hd p (mem_filter.mp hp).1).1 (hd p (mem_filter.mp hp).1).2
    _ ≤ _ := by
      apply prod_le_prod_of_subset_of_one_le₀
      · intro p hp
        exact (hP p (mem_filter.mp hp).1).mem_primeFactors (mem_filter.mp hp).2 hj
      · intros; positivity
      · intro p _ _
        exact le_add_of_nonneg_right (by positivity)

/-- Prime divisors above B^1000 have uniformly negligible reciprocal mass
on every fixed logarithmic size range. -/
theorem large_divisor_inverse_square_bound (κ : ℝ) :
    ∀ᶠ B : ℕ in atTop, ∀ (b : ℕ) (S : Finset ℕ), b ≠ 0 →
      (b : ℝ) ≤ Real.exp (κ * B) → S ⊆ b.primeFactors →
      (∀ p ∈ S, auxiliaryCutoff B ≤ p) →
      (∏ p ∈ S, (1 - 1 / (p : ℝ))⁻¹) ^ 2 ≤ Real.exp 1 := by
  have hlim : Tendsto (fun B : ℕ => (4 * κ / Real.log 2) *
      ((B : ℝ) / (auxiliaryCutoff B : ℝ))) atTop (𝓝 0) := by
    have h := ((polynomial_div_primeCutoff_tendsto_zero (k := 1) (by norm_num)).comp
      tendsto_natCast_atTop_atTop).const_mul (4 * κ / Real.log 2)
    simpa only [Function.comp_def, auxiliaryCutoff, Nat.cast_pow, pow_one, mul_zero] using h
  filter_upwards [hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop 1] with B hsmall hB
  intro b S hb hbsize hS hcut
  have hP0 : (0 : ℝ) < auxiliaryCutoff B := by exact_mod_cast pow_pos (Nat.zero_lt_of_lt hB) 1000
  have hprime : ∀ p ∈ S, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hS hp)
  have hprod : (∏ p ∈ S, p) ∣ b :=
    (prod_dvd_prod_of_subset _ _ id hS).trans (Nat.prod_primeFactors_dvd b)
  have hcard : (S.card : ℝ) * Real.log 2 ≤ κ * B := by
    refine (selectedPrime_card_log_bound S hprime).trans ?_
    have hle : (∏ p ∈ S, p : ℕ) ≤ b := Nat.le_of_dvd (Nat.pos_of_ne_zero hb) hprod
    have hp0 : (0 : ℝ) < (∏ p ∈ S, p : ℕ) := by exact_mod_cast prod_pos (fun p hp => (hprime p hp).pos)
    have hle' : (∏ p ∈ S, p : ℕ) ≤ (b : ℝ) := by exact_mod_cast hle
    have hbpos : (0 : ℝ) < b := by exact_mod_cast Nat.pos_of_ne_zero hb
    exact (Real.log_le_log hp0 hle').trans
      (by simpa only [Real.log_exp] using Real.log_le_log hbpos hbsize)
  have hinv := inverseSelectedPrimeOdds_le hP0 (by norm_num : (0 : ℝ) ≤ 1)
    le_rfl S hprime (fun p hp => by exact_mod_cast hcut p hp)
  have hs0 : 0 ≤ ∏ p ∈ S, (1 - 1 / (p : ℝ))⁻¹ := by
    apply prod_nonneg
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hprime p hp).two_le
    have hinvp : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    exact inv_nonneg.mpr (by linarith)
  calc
    _ ≤ (Real.exp (2 * (S.card : ℝ) / auxiliaryCutoff B)) ^ 2 := pow_le_pow_left₀ hs0 hinv 2
    _ = Real.exp (4 * (S.card : ℝ) / auxiliaryCutoff B) := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ Real.exp 1 := by
      apply Real.exp_le_exp.mpr
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hcard' := (le_div_iff₀ hlog2).mpr hcard
      have h := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcard' (by norm_num : (0 : ℝ) ≤ 4)) hP0.le
      apply h.trans
      calc
        _ = (4 * κ / Real.log 2) * ((B : ℝ) / (auxiliaryCutoff B : ℝ)) := by ring
        _ ≤ 1 := hsmall

end JointDickman

end OAI
