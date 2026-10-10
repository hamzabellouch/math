import OAI.NumberTheory.JointDickman.Arithmetic.RegularityPrimeSums

namespace OAI

/-! # Quantitative choices for the regularity Chernoff bounds -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem exists_prefix_tilt {τ : ℝ} (hτ : 0 < τ) :
    ∃ s : ℝ, 0 < s ∧ s ≤ τ ∧ s ≤ 1 / 10 ∧ Real.exp s ≤ 2 ∧ Real.exp (-s) ≤ 2 ∧
      ∀ g : ℝ, 0 ≤ g → g ≤ 1 →
        -s * τ + (g / 2) * (Real.exp s - 1 - s) ≤ -s * τ / 2 ∧
        -s * τ + (g / 2) * (Real.exp (-s) - 1 + s) ≤ -s * τ / 2 := by
  let s := min τ (1 / 10 : ℝ)
  have hs : 0 < s := lt_min hτ (by norm_num)
  have hsτ : s ≤ τ := min_le_left _ _
  have hs1 : s ≤ 1 / 10 := min_le_right _ _
  have hp := Real.abs_exp_sub_one_sub_id_le (show |s| ≤ 1 by rw [abs_of_pos hs]; linarith)
  have hn := Real.abs_exp_sub_one_sub_id_le (show |-s| ≤ 1 by rw [abs_neg, abs_of_pos hs]; linarith)
  have hp0 : 0 ≤ Real.exp s - 1 - s := by linarith [Real.add_one_le_exp s]
  have hn0 : 0 ≤ Real.exp (-s) - 1 + s := by linarith [Real.add_one_le_exp (-s)]
  have hp2 := (abs_le.mp hp).2
  have hn2 := (abs_le.mp hn).2
  refine ⟨s, hs, hsτ, hs1, ?_, ?_, ?_⟩
  · nlinarith [sq_nonneg (s - 1 / 10)]
  · calc
      Real.exp (-s) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
      _ ≤ 2 := by norm_num
  · intro g hg hg1
    have hst := mul_nonneg hs.le (sub_nonneg.mpr hsτ)
    constructor
    · have hmul := mul_nonneg (sub_nonneg.mpr hg1) hp0
      nlinarith
    · have hmul := mul_nonneg (sub_nonneg.mpr hg1) hn0
      nlinarith

theorem tail_tilt_margin :
    0 < (1 / 2 : ℝ) * (1 - Real.exp (-(1 / 10 : ℝ))) - (2 / 5 : ℝ) * (1 / 10) := by
  have h := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le
    (show |-(1 / 10 : ℝ)| ≤ 1 by norm_num))).2
  norm_num at h ⊢
  linarith

/-- The two prefix Markov factors tend to zero, uniformly in the choice of
any fixed finite grid after its points are instantiated. -/
theorem regularity_prefix_chernoff_decay
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {τ : ℝ} (hτ : 0 < τ) :
    ∃ s : ℝ, 0 < s ∧ Real.exp s ≤ 2 ∧ Real.exp (-s) ≤ 2 ∧
      ∀ c g : ℝ, 0 < c → 0 < g → g ≤ 1 →
      Tendsto (fun B : ℕ => Real.exp (-s * (g / 2 + τ) * auxiliaryLogLength B +
        ((Real.exp s - 1) / 2) *
          (∑ p ∈ largePrimeSet (Real.exp (c * (B : ℝ) ^ g)) (auxiliaryCutoff B), 1 / (p : ℝ))))
        atTop (𝓝 0) ∧
      Tendsto (fun B : ℕ => Real.exp (s * (g / 2 - τ) * auxiliaryLogLength B +
        ((Real.exp (-s) - 1) / 2) *
          (∑ p ∈ largePrimeSet (Real.exp (c * (B : ℝ) ^ g)) (auxiliaryCutoff B), 1 / (p : ℝ))))
        atTop (𝓝 0) := by
  obtain ⟨s, hs, _hsτ, _hs1, he, hen, hmargin⟩ := exists_prefix_tilt hτ
  refine ⟨s, hs, he, hen, ?_⟩
  intro c g hc hg hg1
  let m := fun B : ℕ => ∑ p ∈ largePrimeSet (Real.exp (c * (B : ℝ) ^ g)) (auxiliaryCutoff B), 1 / (p : ℝ)
  have hm : Tendsto (fun B => m B / auxiliaryLogLength B) atTop (𝓝 g) :=
    regularity_prefix_prime_sum_tendsto hM hc hg
  have hpos : -s * (g / 2 + τ) + ((Real.exp s - 1) / 2) * g < 0 := by
    have h := (hmargin g hg.le hg1).1
    nlinarith [mul_pos hs hτ]
  have hneg : s * (g / 2 - τ) + ((Real.exp (-s) - 1) / 2) * g < 0 := by
    have h := (hmargin g hg.le hg1).2
    nlinarith [mul_pos hs hτ]
  have hℓ : ∀ᶠ B : ℕ in atTop, auxiliaryLogLength B ≠ 0 :=
    (auxiliaryLogLength_tendsto.eventually_gt_atTop 0).mono (fun _ h => ne_of_gt h)
  constructor
  · have hlim := (hm.const_mul ((Real.exp s - 1) / 2)).const_add (-s * (g / 2 + τ))
    have hprod := hlim.neg_mul_atTop hpos auxiliaryLogLength_tendsto
    apply Real.tendsto_exp_atBot.comp (hprod.congr' ?_)
    filter_upwards [hℓ] with B hB
    dsimp [m]
    field_simp
  · have hlim := (hm.const_mul ((Real.exp (-s) - 1) / 2)).const_add (s * (g / 2 - τ))
    have hprod := hlim.neg_mul_atTop hneg auxiliaryLogLength_tendsto
    apply Real.tendsto_exp_atBot.comp (hprod.congr' ?_)
    filter_upwards [hℓ] with B hB
    dsimp [m]
    field_simp

end JointDickman

end OAI
