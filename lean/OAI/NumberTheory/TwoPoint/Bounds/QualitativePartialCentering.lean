import OAI.NumberTheory.TwoPoint.Bounds.DilatedRoughBins
import OAI.NumberTheory.TwoPoint.Bounds.ComplexPartialBounds
import OAI.NumberTheory.TwoPoint.Bounds.ComplexBinWindows
import OAI.NumberTheory.TwoPoint.Walks.TupleSmoothCost

namespace OAI

/-! Direct dilation gives qualitative centering for the actual complex
partial-tuple terms. The eventual cutoff is allowed to depend on the fixed
finite prime families, while the analytic constant is independent of them. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

lemma qualitative_dilated_fixed_factors (hM : PrimeReciprocalInput)
    (hMRT : MRTShortExponentialInput) {F G : ℕ → ℂ}
    (hFm : Multiplicative F) (hGm : Multiplicative G)
    (hF : OneBounded F) (hG : OneBounded G)
    (hnp : UniformlyNonpretentious F ∨ UniformlyNonpretentious G)
    (h : ℕ) (hh : 0 < h) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℝ in atTop,
      ∀ (u : ℕ), 0 < u → ∀ M τ : ℝ, 1 < τ → τ < 2 →
      Real.exp (B ^ (9999 / 10000 : ℝ)) / τ ≤ M →
      M ≤ Real.exp (C₀ * B ^ (2 : ℕ)) →
      ∀ᶠ Y : ℕ in atTop, ∀ Z : Finset ℕ,
      (∀ z ∈ Z, M < (z : ℝ) ∧ (z : ℝ) ≤ τ * M ∧
        HasNoPrimeFactorBelow (Real.exp (B ^ (9999 / 10000 : ℝ))) z) →
      ‖weightedRoughShiftAverage (fun n => F (u * n)) (fun n => G (u * n))
        Z (fun _ => 1) h Y‖ ≤
        C * B ^ (-11 / 10 : ℝ) * smoothReciprocalProduct u.primeFactors (1 / 2 : ℝ) := by
  rcases hnp with hnp | hnp
  · obtain ⟨C, hC, hb⟩ := qualitative_dilated_rough_shifts_real_bins hM hMRT hnp hF h hh C₀ hC₀
    refine ⟨C, hC, ?_⟩
    filter_upwards [hb] with B hb
    intro u hu M τ hτ₁ hτ₂ hlow hupp
    filter_upwards [hb ∅ M τ hτ₁ hτ₂ hlow hupp u hu] with Y hY
    intro Z hZ
    exact hY F G hFm hF hG (fun _ _ _ => rfl) Z (fun _ => 1) hZ (by simp)
  · obtain ⟨C, hC, hb⟩ := qualitative_dilated_rough_shifts_real_bins_right hM hMRT hnp hG h hh C₀ hC₀
    refine ⟨C, hC, ?_⟩
    filter_upwards [hb] with B hb
    intro u hu M τ hτ₁ hτ₂ hlow hupp
    filter_upwards [hb ∅ M τ hτ₁ hτ₂ hlow hupp u hu] with Y hY
    intro Z hZ
    exact hY F G hF hGm hG (fun _ _ _ => rfl) Z (fun _ => 1) hZ (by simp)

theorem qualitative_complex_partial_bin (hM : PrimeReciprocalInput)
    (hMRT : MRTShortExponentialInput) {F G : ℕ → ℂ}
    (hFm : Multiplicative F) (hGm : Multiplicative G)
    (hF : OneBounded F) (hG : OneBounded G)
    (hnp : UniformlyNonpretentious F ∨ UniformlyNonpretentious G)
    (h : ℕ) (hh : 0 < h) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℝ in atTop,
      ∀ (J : ℕ) (P : Fin J → Finset ℕ),
      (∀ i, ∀ p ∈ P i, p.Prime) →
      (∀ i j, j ≠ i → Disjoint (P i) (P j)) →
      (∀ i, ∀ p ∈ P i, Real.exp (B ^ (9999 / 10000 : ℝ)) ≤ (p : ℝ)) →
      ∀ (I : Finset (Fin J)), I.Nonempty → ∀ q : ℕ, 0 < q →
      (∀ y : (i : {i // i ∉ I}) → P i,
        smoothReciprocalProduct (∏ i, (y i).val).primeFactors (1 / 2 : ℝ) ≤ 2) →
      ∀ (η : ℝ), 0 < η → Real.exp (2 * η) < 2 → ∀ j : ℤ,
      Real.exp ((j : ℝ) * η) ≤ Real.exp (C₀ * B ^ (2 : ℕ)) →
      ∀ᶠ X : ℕ in atTop, ∀ eligible : ℕ → ℕ → Prop,
      (∀ d q, eligible d q → actualPaddingBin η (Real.log d) j q) →
      ‖positivePrefix (tupleComplexPartialProfile P I q eligible F G h) X / (X : ℂ)‖ ≤
        (2 * C * B ^ (-11 / 10 : ℝ) *
          smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ)) *
        ((1 / (q : ℝ)) * ∏ i : {i // i ∉ I}, primeHarmonicMass (P i)) := by
  obtain ⟨C, hC, hb⟩ := qualitative_dilated_fixed_factors hM hMRT hFm hGm hF hG hnp h hh C₀ hC₀
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with B hb hB
  intro J P hp hd hlarge I hI q hq hcost η hη hηtwo j hj
  let τ := Real.exp (2 * η)
  have hτ : 1 < τ := Real.one_lt_exp_iff.mpr (by positivity)
  have hτp : 0 < τ := Real.exp_pos _
  let E := 2 * C * B ^ (-11 / 10 : ℝ) *
    smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ)
  have hE : 0 ≤ E := mul_nonneg (by positivity)
    (smoothReciprocalProduct_nonneg _ (fun _ hp => Nat.prime_of_mem_primeFactors hp)
      _ (by norm_num))
  have hall : ∀ᶠ X : ℕ in atTop, ∀ y : (i : {i // i ∉ I}) → P i,
      ∀ eligible : ℕ → ℕ → Prop,
      (∀ d q, eligible d q → actualPaddingBin η (Real.log d) j q) →
      ‖weightedRoughShiftAverage
        (fun n => F ((q * ∏ i, (y i).val) * n))
        (fun n => G ((q * ∏ i, (y i).val) * n))
        ((primeTupleSlice P I).filter (fun z => eligible ((∏ i, (y i).val) * z) q))
        (fun _ => 1) h (X / (q * ∏ i, (y i).val))‖ ≤ E := by
    apply Filter.eventually_all.mpr
    intro y
    let t : ℕ := ∏ i, (y i).val
    let u := q * t
    let M := enlargedBinStart η j u
    have ht : 0 < t := prod_pos fun i _ => (hp i _ (y i).property).pos
    have hu : 0 < u := Nat.mul_pos hq ht
    have hMupper : M ≤ Real.exp (C₀ * B ^ (2 : ℕ)) :=
      enlargedBinStart_upper η hη.le j u hu _ hj
    by_cases hMlower : Real.exp (B ^ (9999 / 10000 : ℝ)) / τ ≤ M
    · have hwin := (tendsto_nat_div_atTop u hu).eventually
        (hb u hu M τ hτ hηtwo hMlower hMupper)
      filter_upwards [hwin] with X hX
      intro eligible hel
      have hZ : ∀ z ∈ (primeTupleSlice P I).filter (fun z => eligible (t * z) q),
          M < (z : ℝ) ∧ (z : ℝ) ≤ τ * M ∧
          HasNoPrimeFactorBelow (Real.exp (B ^ (9999 / 10000 : ℝ))) z := by
        intro z hz
        obtain ⟨hz, he⟩ := mem_filter.mp hz
        have hzpos := primeTupleSlice_pos P I hp hz
        have hw := enlarged_partial_bin_window q t z hq ht hzpos η hη j (hel _ _ he)
        refine ⟨hw.1, hw.2, ?_⟩
        intro p hprime hsmall hdiv
        obtain ⟨i, _, hi⟩ := prime_dvd_primeTupleSlice P I hp hz hprime hdiv
        exact (not_lt_of_ge (hlarge i p hi)) hsmall
      apply (hX _ hZ).trans
      have hc := mul_le_mul_of_nonneg_left (dilated_tuple_smooth_cost q t hq ht (hcost y))
        (show 0 ≤ C * B ^ (-11 / 10 : ℝ) by positivity)
      exact hc.trans_eq (by dsimp only [E]; ring)
    · refine Filter.Eventually.of_forall ?_
      intro X eligible hel
      have hempty : (primeTupleSlice P I).filter (fun z => eligible (t * z) q) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro z hz
        obtain ⟨hz, he⟩ := mem_filter.mp hz
        have hw := enlarged_partial_bin_window q t z hq ht
          (primeTupleSlice_pos P I hp hz) η hη j (hel _ _ he)
        exact hMlower (rough_bin_forces_start_lower hτp
          (primeTupleSlice_lower P I hp _ hlarge hI hz) hw.2)
      change ‖weightedRoughShiftAverage (fun n => F (u * n)) (fun n => G (u * n))
        ((primeTupleSlice P I).filter (fun z => eligible (t * z) q)) (fun _ => 1) h (X / u)‖ ≤ E
      rw [hempty]
      simpa only [weightedRoughShiftAverage, weightedRoughShiftProfile, sum_empty,
        positivePrefix, sum_const_zero, zero_div, norm_zero] using hE
  filter_upwards [hall, eventually_ge_atTop 1] with X hX hXpos
  intro eligible hel
  exact complex_partial_tuple_prefix_bound P hp hd I q hq eligible F G h X
    (by omega) E hE (fun y => hX y eligible hel)

end TwoPointCorrelations

end OAI
