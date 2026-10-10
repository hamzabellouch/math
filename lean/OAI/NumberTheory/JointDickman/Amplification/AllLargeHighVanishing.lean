import OAI.NumberTheory.JointDickman.Amplification.AllLargeHighExpectation
import OAI.NumberTheory.JointDickman.Amplification.LargeHighVanishing

namespace OAI

/-! # Summing every cardinality class of a large high-endpoint addition -/

namespace JointDickman
open Finset Filter
open scoped Topology

noncomputable def allLargeClassError (K η ν : ℝ) (B : ℕ) : ℝ :=
  (K/η)*(Real.log B+1)^5/(B : ℝ)^((32/100 : ℝ)-ν)

theorem log_add_one_fifth_div_rpow_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto (fun B : ℝ => (Real.log B+1)^5/B^c) atTop (𝓝 0) := by
  have ht : Tendsto (fun B : ℝ => 32*(Real.log B)^5/B^c) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast,mul_zero,mul_div_assoc] using
      (log_power_div_power_tendsto_zero (5 : ℕ) hc).const_mul 32
  apply squeeze_zero' _ _ ht
  · filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1,eventually_gt_atTop (0 : ℝ)] with B hlog hB
    positivity
  · filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1,eventually_gt_atTop (0 : ℝ)] with B hlog hB
    apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hB.le _)
    have hh : Real.log B+1 ≤ 2*Real.log B := by linarith
    have hp := pow_le_pow_left₀ (by linarith : 0 ≤ Real.log B+1) hh 5
    nlinarith

theorem allLargeClassError_tendsto {K η ν : ℝ} (hν : ν < 32/100) :
    Tendsto (allLargeClassError K η ν) atTop (𝓝 0) := by
  have hh := ((log_add_one_fifth_div_rpow_tendsto (sub_pos.mpr hν)).comp
    tendsto_natCast_atTop_atTop).const_mul (K/η)
  unfold allLargeClassError
  simpa only [mul_zero,mul_div_assoc,Function.comp_apply] using hh

/-- All cardinality classes together still have vanishing expected
multiplicity. The only loss from summing them is two logarithmic powers. -/
theorem all_large_high_class_vanishing
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {L k : ℕ} (hk : k ∈ Icc 1 L) {g Δ δ ε η : ℝ}
    (hkg : (k : ℝ)/L = g) (hg : 0 < g) (hg1 : g ≤ 1)
    (hΔ : 0 < Δ) (hgap : 2*Δ < g)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) (hε : 0 < ε) (hη : 0 < η) :
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τ : ℝ, 0 < τ → τ ≤ τ₀ →
      largeMultiplicityLoss Δ δ τ ε < 4/100 →
      ∃ E : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧ ∀ᶠ B : ℕ in atTop,
        ∀ (C : ℝ) (A D V : Finset ℕ) (j : ℕ),
          A ⊆ auxiliaryPrimes B → D ⊆ auxiliaryPrimes B → V ⊆ auxiliaryPrimes B →
          RegularPrimeSet B L τ C A → RegularPrimeSet B L τ C D → RegularPrimeSet B L τ C V →
          (∏ p ∈ A, p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) →
          0 < j → j ≤ auxiliaryCutoff B → (j : ℝ) ≤ (B : ℝ)^2 →
          η*(B : ℝ)^(32/100 : ℝ) ≤ j →
          tiltedAllLargeHighPairCount B L k j τ C Δ A D V ≤ E B := by
  obtain ⟨τ₁,hτ₁,hbound⟩ := large_high_class_error_bound hFord hM hk hkg hg hg1 hΔ hgap hδ hδ1 hε hη
  refine ⟨min τ₁ (1/2),lt_min hτ₁ (by norm_num),?_⟩
  intro τ hτ hτsmall hloss
  have hτ₁' : τ ≤ τ₁ := hτsmall.trans (min_le_left _ _)
  have hτhalf : τ ≤ 1/2 := hτsmall.trans (min_le_right _ _)
  obtain ⟨K,hK,_,hestimate⟩ := hbound τ hτ hτ₁' hloss
  let ν := largeMultiplicityBase+largeMultiplicityLoss Δ δ τ ε
  have hν : ν < 32/100 := by
    have hh := largeMultiplicityBase_bounds.2
    dsimp only [ν]
    linarith
  refine ⟨allLargeClassError K η ν,allLargeClassError_tendsto hν,?_⟩
  filter_upwards [hestimate,auxiliaryLogLength_between,eventually_gt_atTop 1] with B hB hℓB hB1
  intro C A D V j hA hD hV hAr hDr hVr hAsize hj hcut hjB hjlow
  rw [tiltedAllLargeHighPairCount_eq_sum A D V hk hτhalf hℓB.1 hVr]
  let N := ⌊auxiliaryLogLength B⌋₊+1
  have hN : (N : ℝ) ≤ Real.log B+1 := by
    have hh := Nat.floor_le hℓB.1
    dsimp only [N]
    push_cast
    linarith [hℓB.2]
  have hlog : 0 ≤ Real.log B := Real.log_nonneg (by exact_mod_cast hB1.le)
  have hE : 0 ≤ largeClassError K η ν B := by
    unfold largeClassError
    positivity
  calc
    _ ≤ ∑ d ∈ range N, ∑ f ∈ range N, largeClassError K η ν B := by
      apply sum_le_sum
      intro d _
      apply sum_le_sum
      intro f _
      exact hB C A D V j d f hA hD hV hAr hDr hVr hAsize hj hcut hjB hjlow
    _ = (N : ℝ)^2*largeClassError K η ν B := by
      simp only [sum_const,card_range,nsmul_eq_mul]
      ring
    _ ≤ (Real.log B+1)^2*largeClassError K η ν B :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hN 2) hE
    _ = _ := by unfold largeClassError allLargeClassError; ring

end JointDickman

end OAI
