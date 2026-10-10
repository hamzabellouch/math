import OAI.NumberTheory.JointDickman.Arithmetic.ConditionalPrimeParameters
import OAI.NumberTheory.JointDickman.Arithmetic.PrimeIndicatorErrors

namespace OAI

/-! # Uniform prefix means after removing bounded prime products -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem prefix_reciprocal_mean_tendsto
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {g : ℝ}
    (hg : 0 < g) (hg1 : g ≤ 1) :
    Tendsto (fun B : ℕ => (∑ p ∈ primePrefix B g (auxiliaryPrimes B), 1/(p : ℝ))/
      auxiliaryLogLength B) atTop (𝓝 g) := by
  have h := tilt_prefix_mass_tendsto hM (by norm_num : (0 : ℝ) < 4) (by norm_num) hg hg1
  apply h.congr'
  filter_upwards [auxiliaryCutoff_tendsto.eventually_ge_atTop 6] with B hB
  rw [full_cutoff_prime_mass B _ hB]
  congr 2
  apply inter_eq_right.mpr
  unfold primePrefix
  split_ifs
  · exact filter_subset _ _
  · exact subset_rfl

theorem remaining_parameter_restricted_sum (P E Q : Finset ℕ) :
    (∑ p ∈ P ∩ Q, remainingPrimeParameter E p) =
      ∑ p ∈ (P \ E) ∩ Q, 1/(2*(p : ℝ)-1) := by
  calc
    _ = ∑ p ∈ (P \ E) ∩ Q, remainingPrimeParameter E p := by
      symm
      apply sum_subset
      · exact inter_subset_inter sdiff_subset subset_rfl
      · intro p hp hn
        have hpE : p ∈ E := by
          by_contra he
          exact hn (mem_inter.mpr ⟨mem_sdiff.mpr ⟨(mem_inter.mp hp).1,he⟩,(mem_inter.mp hp).2⟩)
        simp [remainingPrimeParameter,hpE]
    _ = _ := by
      apply sum_congr rfl
      intro p hp
      simp [remainingPrimeParameter,(mem_sdiff.mp (mem_inter.mp hp).1).2]

/-- A fixed exponential product removes only a bounded total parameter
error. The resulting normalized error tends to zero uniformly in that
product; this will be applied to the first coefficient and a fixed addition. -/
theorem tilted_prefix_mean_uniform
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {κ g : ℝ}
    (hκ : 0 < κ) (hg : 0 < g) (hg1 : g ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ B : ℕ in atTop, ∀ E : Finset ℕ, E ⊆ auxiliaryPrimes B →
      (∏ p ∈ E, p : ℕ) ≤ Real.exp (κ*B) →
      |(∑ p ∈ (auxiliaryPrimes B \ E) ∩ primePrefix B g (auxiliaryPrimes B),
          1/(2*(p : ℝ)-1))/auxiliaryLogLength B-g/2| ≤ ε := by
  let m := fun B : ℕ => ∑ p ∈ primePrefix B g (auxiliaryPrimes B), 1/(p : ℝ)
  have hm : Tendsto (fun B : ℕ => m B/auxiliaryLogLength B) atTop (𝓝 g) :=
    prefix_reciprocal_mean_tendsto hM hg hg1
  have herr : Tendsto (fun B : ℕ => 2/auxiliaryLogLength B+
      (1/2 : ℝ)*|m B/auxiliaryLogLength B-g|) atTop (𝓝 0) := by
    have h₂ : Tendsto (fun B : ℕ => (2 : ℝ)/auxiliaryLogLength B) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop auxiliaryLogLength_tendsto
    simpa using h₂.add (((hm.sub_const g).abs).const_mul (1/2 : ℝ))
  filter_upwards [auxiliary_selected_reciprocal_sum_small hκ,
    auxiliaryLogLength_tendsto.eventually_gt_atTop 0,
    herr.eventually (Iio_mem_nhds hε)] with B hsmall hℓ heps
  intro E hE hprod
  have he := remaining_parameter_total_error (fun p hp => auxiliaryPrimes_prime B p hp) hE
  have he' := restricted_indicator_mean_error (D := 2) (auxiliaryPrimes B)
    (primePrefix B g (auxiliaryPrimes B)) (remainingPrimeParameter E)
    (he.trans (by linarith [hsmall E hE hprod]))
  rw [remaining_parameter_restricted_sum] at he'
  have hQ : auxiliaryPrimes B ∩ primePrefix B g (auxiliaryPrimes B) =
      primePrefix B g (auxiliaryPrimes B) := by
    apply inter_eq_right.mpr
    unfold primePrefix
    split_ifs
    · exact filter_subset _ _
    · exact subset_rfl
  rw [hQ] at he'
  let x := ∑ p ∈ (auxiliaryPrimes B \ E) ∩ primePrefix B g (auxiliaryPrimes B),
    1/(2*(p : ℝ)-1)
  have hdiv : |x/auxiliaryLogLength B-(1/2 : ℝ)*(m B/auxiliaryLogLength B)| ≤
      2/auxiliaryLogLength B := by
    rw [← mul_div_assoc,← sub_div,abs_div,abs_of_pos hℓ]
    exact div_le_div_of_nonneg_right he' hℓ.le
  have htri := abs_sub_le (x/auxiliaryLogLength B) ((1/2 : ℝ)*(m B/auxiliaryLogLength B)) (g/2)
  have hmid : |(1/2 : ℝ)*(m B/auxiliaryLogLength B)-g/2| =
      (1/2 : ℝ)*|m B/auxiliaryLogLength B-g| := by
    rw [show (1/2 : ℝ)*(m B/auxiliaryLogLength B)-g/2 =
      (1/2 : ℝ)*(m B/auxiliaryLogLength B-g) by ring,abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 1/2)]
  rw [hmid] at htri
  dsimp only [x] at htri hdiv
  linarith

end JointDickman

end OAI
