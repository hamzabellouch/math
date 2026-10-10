import OAI.NumberTheory.JointDickman.Amplification.ManuscriptAdditionProduct
import OAI.NumberTheory.JointDickman.Arithmetic.ConditionalPrimeParameters
import OAI.NumberTheory.JointDickman.Amplification.ProductComparison

namespace OAI

/-! # Addition products after fixing the first coefficient -/

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def conditionalAdditionParameter (A : Finset ℕ) (p : ℕ) : ℝ :=
  remainingPrimeParameter A p / 2

theorem conditionalAdditionParameter_bounds (A : Finset ℕ) {p : ℕ} (hp : 2 ≤ p) :
    0 ≤ conditionalAdditionParameter A p ∧ conditionalAdditionParameter A p ≤ 1 := by
  obtain ⟨h0, h1⟩ := remainingPrimeParameter_mem_Icc A hp
  unfold conditionalAdditionParameter
  constructor <;> linarith only [h0, h1]

theorem conditionalAdditionParameter_error (A : Finset ℕ) {p : ℕ} (hp : 2 ≤ p) :
    |conditionalAdditionParameter A p - (1 / 4 : ℝ) / p| ≤
      1 / (p : ℝ)^2 + if p ∈ A then 1 / (p : ℝ) else 0 := by
  classical
  have hpR : (0 : ℝ) < p := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hp)
  by_cases ha : p ∈ A
  · simp only [conditionalAdditionParameter, remainingPrimeParameter, ha, ite_true, zero_div,
      zero_sub, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / 4 : ℝ) / p)]
    have hd : (1 / 4 : ℝ) / p ≤ 1 / (p : ℝ) := div_le_div_of_nonneg_right (by norm_num) hpR.le
    linarith [show (0 : ℝ) ≤ 1 / (p : ℝ)^2 by positivity]
  · have heq : conditionalAdditionParameter A p - (1 / 4 : ℝ) / p =
        (1 / (2 * (p : ℝ) - 1) - (1 / 2 : ℝ) / p) / 2 := by
      simp only [conditionalAdditionParameter, remainingPrimeParameter, ha, ite_false]
      ring
    rw [heq, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have he := unselected_parameter_error hp
    simp only [ha, ite_false, add_zero]
    linarith [show (0 : ℝ) ≤ 1 / (p : ℝ)^2 by positivity]

theorem selected_reciprocal_bound {B : ℕ} {A : Finset ℕ} {κ : ℝ}
    (hB : 1 < B) (hA : A ⊆ auxiliaryPrimes B)
    (hsize : (∏ p ∈ A, p : ℕ) ≤ Real.exp (κ * B)) :
    (∑ p ∈ A, 1 / (p : ℝ)) ≤ (κ / Real.log 2) * (B : ℝ) / auxiliaryCutoff B := by
  have hP0 : (0 : ℝ) < auxiliaryCutoff B := by
    exact_mod_cast (pow_pos (Nat.zero_lt_of_lt hB) 1000)
  have hprime : ∀ p ∈ A, p.Prime := fun p hp => auxiliaryPrimes_prime B p (hA hp)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcard : (A.card : ℝ) ≤ κ * B / Real.log 2 := by
    apply (le_div_iff₀ hlog2).mpr
    refine (selectedPrime_card_log_bound A hprime).trans ?_
    have hn0 : (0 : ℝ) < (∏ p ∈ A, p : ℕ) := by
      exact_mod_cast prod_pos (fun p hp => (hprime p hp).pos)
    simpa only [Real.log_exp] using Real.log_le_log hn0 hsize
  calc
    _ ≤ ∑ _p ∈ A, 1 / (auxiliaryCutoff B : ℝ) := sum_le_sum (fun p hp =>
      one_div_le_one_div_of_le hP0 (mem_filter.mp (hA hp)).2.le)
    _ = (A.card : ℝ) / auxiliaryCutoff B := by simp [div_eq_mul_inv]
    _ ≤ (κ * B / Real.log 2) / auxiliaryCutoff B := div_le_div_of_nonneg_right hcard hP0.le
    _ = _ := by ring

theorem conditionalAdditionParameter_total_error {B : ℕ} {A P : Finset ℕ} {κ : ℝ}
    (hB : 1 < B) (hA : A ⊆ auxiliaryPrimes B) (hP : P ⊆ auxiliaryPrimes B)
    (hsize : (∏ p ∈ A, p : ℕ) ≤ Real.exp (κ * B)) :
    (∑ p ∈ P, |conditionalAdditionParameter A p - (1 / 4 : ℝ) / p|) ≤
      (1 + (κ / Real.log 2) * B) / auxiliaryCutoff B := by
  classical
  have hP0 : auxiliaryCutoff B ≠ 0 := pow_ne_zero _ (Nat.ne_of_gt (Nat.zero_lt_of_lt hB))
  have hsq := sum_reciprocal_square_tail P hP0 (fun p hp => by
    exact_mod_cast (mem_filter.mp (hP hp)).2)
  have hsum := sum_le_sum (fun p hp => conditionalAdditionParameter_error A
    (auxiliaryPrimes_prime B p (hP hp)).two_le)
  have hsub : P.filter (fun p => p ∈ A) ⊆ A := fun p hp => (mem_filter.mp hp).2
  have hsel : (∑ p ∈ P, if p ∈ A then 1 / (p : ℝ) else 0) ≤
      (κ / Real.log 2) * B / auxiliaryCutoff B := by
    rw [← sum_filter]
    exact (sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)).trans
      (selected_reciprocal_bound hB hA hsize)
  rw [sum_add_distrib] at hsum
  calc
    _ ≤ (∑ p ∈ P, 1 / (p : ℝ)^2) + (∑ p ∈ P, if p ∈ A then 1 / (p : ℝ) else 0) := hsum
    _ ≤ 1 / (auxiliaryCutoff B : ℝ) + (κ / Real.log 2) * B / auxiliaryCutoff B :=
      add_le_add hsq hsel
    _ = _ := by ring

open Classical in
theorem bernoulliSubsetMass_event_perturb {α : Type*} [DecidableEq α]
    (P : Finset α) (q r : α → ℝ) (E : Finset α → Prop)
    (hq : ∀ p ∈ P, 0 ≤ q p ∧ q p ≤ 1) (hr : ∀ p ∈ P, 0 ≤ r p ∧ r p ≤ 1) :
    (∑ S ∈ P.powerset, if E S then bernoulliSubsetMass P q S else 0) ≤
      (∑ S ∈ P.powerset, if E S then bernoulliSubsetMass P r S else 0) +
        2 * ∑ p ∈ P, |q p - r p| := by
  classical
  have hh : (∑ S ∈ P.powerset, if E S then bernoulliSubsetMass P q S else 0) -
      (∑ S ∈ P.powerset, if E S then bernoulliSubsetMass P r S else 0) ≤
        ∑ S ∈ P.powerset, |bernoulliSubsetMass P q S - bernoulliSubsetMass P r S| := by
    rw [← sum_sub_distrib]
    apply sum_le_sum
    intro S _
    split_ifs
    · exact le_abs_self _
    · simpa only [sub_self] using abs_nonneg (bernoulliSubsetMass P q S - bernoulliSubsetMass P r S)
  have hl := bernoulliSubsetMass_l1_perturb P q r hq hr
  linarith only [hh, hl]


theorem additionPrimes_subset_auxiliary (B : ℕ) (Y : ℝ) :
    additionPrimes B Y ⊆ auxiliaryPrimes B := by
  intro p hp
  obtain ⟨hpp, hrough⟩ := mem_filter.mp hp
  apply mem_filter.mpr
  refine ⟨Nat.mem_primesLE.mpr ⟨?_, (Nat.mem_primesLE.mp hpp).2⟩, hrough⟩
  exact (Nat.mem_primesLE.mp hpp).1.trans
    (Nat.floor_mono (Real.exp_le_exp.mpr (min_le_right Y (4 * (B : ℝ)))))

theorem conditionalAddition_error_small (κ : ℝ) :
    ∀ᶠ B : ℕ in atTop, 0 < (B : ℝ) ∧
      2 * ((1 + (κ / Real.log 2) * B) / auxiliaryCutoff B) ≤ 1 / (8 * B) := by
  have h1 := ((polynomial_div_primeCutoff_tendsto_zero (k := 1) (by norm_num)).comp
    tendsto_natCast_atTop_atTop).const_mul 16
  have h2 := ((polynomial_div_primeCutoff_tendsto_zero (k := 2) (by norm_num)).comp
    tendsto_natCast_atTop_atTop).const_mul (16 * (κ / Real.log 2))
  have ht : Tendsto (fun B : ℕ =>
      (16 * (B : ℝ) * (1 + (κ / Real.log 2) * B)) / auxiliaryCutoff B)
      atTop (𝓝 0) := by
    convert h1.add h2 using 1
    · ext B
      simp only [auxiliaryCutoff, Nat.cast_pow, pow_one, Function.comp_def]
      ring
    · simp only [mul_zero, add_zero]
  filter_upwards [ht.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop 1] with B hb hB
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (Nat.zero_lt_of_lt hB)
  refine ⟨hB0, ?_⟩
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * B)).mpr
  convert hb using 1
  ring

open Classical in
noncomputable def conditionalAdditionLogIntervalMass (B : ℕ) (A : Finset ℕ) (Y v H : ℝ) : ℝ :=
  ∑ S ∈ (additionPrimes B Y).powerset,
    if v ≤ Real.log (∏ p ∈ S, p : ℕ) ∧ Real.log (∏ p ∈ S, p : ℕ) ≤ v + H ∧
        Y / 2 ≤ Real.log (∏ p ∈ S, p : ℕ) then
      bernoulliSubsetMass (additionPrimes B Y) (conditionalAdditionParameter A) S else 0

/-- The small-ball estimate survives conditioning on any first coefficient
in the required fixed exponential range. The changed parameters and omitted
coefficient primes are accounted for explicitly. -/
theorem conditional_addition_small_ball
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {H κ : ℝ} (hH : 0 ≤ H) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ (A : Finset ℕ) (Y v : ℝ),
      A ⊆ auxiliaryPrimes B → (∏ p ∈ A, p : ℕ) ≤ Real.exp (κ * B) →
      Real.log (auxiliaryCutoff B) ≤ Y → Y ≤ 8 * B →
      conditionalAdditionLogIntervalMass B A Y v H ≤ K / Y := by
  obtain ⟨K, hK, hbound⟩ := manuscript_addition_small_ball hFord hM hH
  have hlog : Tendsto (fun B : ℕ => Real.log (auxiliaryCutoff B)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp auxiliaryCutoff_tendsto)
  refine ⟨K + 1, by linarith only [hK], ?_⟩
  filter_upwards [hbound, conditionalAddition_error_small κ, hlog.eventually_ge_atTop 1,
    eventually_gt_atTop 1] with B hb he hlogB hB
  intro A Y v hA hsize hY hYB
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one (hlogB.trans hY)
  have hP := additionPrimes_subset_auxiliary B Y
  have hq : ∀ p ∈ additionPrimes B Y, 0 ≤ conditionalAdditionParameter A p ∧
      conditionalAdditionParameter A p ≤ 1 :=
    fun p hp => conditionalAdditionParameter_bounds A (additionPrimes_prime B Y p hp).two_le
  have hr : ∀ p ∈ additionPrimes B Y, 0 ≤ (1 / 4 : ℝ) / p ∧ (1 / 4 : ℝ) / p ≤ 1 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (additionPrimes_prime B Y p hp).two_le
    refine ⟨by positivity, (div_le_one (by linarith)).mpr (by linarith)⟩
  have hh := bernoulliSubsetMass_event_perturb (additionPrimes B Y)
    (conditionalAdditionParameter A) (fun p => (1 / 4 : ℝ) / p)
    (fun S => v ≤ Real.log (∏ p ∈ S, p : ℕ) ∧ Real.log (∏ p ∈ S, p : ℕ) ≤ v + H ∧
      Y / 2 ≤ Real.log (∏ p ∈ S, p : ℕ)) hq hr
  have hh' : conditionalAdditionLogIntervalMass B A Y v H ≤ additionLogIntervalMass B Y v H +
      2 * ∑ p ∈ additionPrimes B Y, |conditionalAdditionParameter A p - (1 / 4 : ℝ) / p| := by
    simpa only [conditionalAdditionLogIntervalMass, additionLogIntervalMass, Nat.cast_prod] using hh
  have herr := conditionalAdditionParameter_total_error hB hA hP hsize
  have htail : 1 / (8 * (B : ℝ)) ≤ 1 / Y := one_div_le_one_div_of_le hY0 hYB
  have hmain := hb Y v hY hYB
  have herr2 := mul_le_mul_of_nonneg_left herr (by norm_num : (0 : ℝ) ≤ 2)
  have hc : K / Y + 1 / Y = (K + 1) / Y := by ring
  rw [← hc]
  linarith only [hh', herr2, he.2, htail, hmain]

end JointDickman

end OAI
