import OAI.NumberTheory.JointDickman.Amplification.LargeAlternativeExpectation
import OAI.NumberTheory.JointDickman.Amplification.LargeMultiplicityExponent

namespace OAI

/-! # The expected multiplicity of a large high-endpoint addition class -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem large_high_alternative_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {L k : ℕ} (hk : k ∈ Icc 1 L) {g Δ δ ε : ℝ}
    (hkg : (k : ℝ)/L = g) (hg : 0 < g) (hg1 : g ≤ 1)
    (hΔ : 0 < Δ) (hgap : 2*Δ < g)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) (hε : 0 < ε) :
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τ : ℝ, 0 < τ → τ ≤ τ₀ →
      ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop,
        ∀ (C : ℝ) (A D V : Finset ℕ) (j d f : ℕ),
          A ⊆ auxiliaryPrimes B → D ⊆ auxiliaryPrimes B → V ⊆ auxiliaryPrimes B →
          RegularPrimeSet B L τ C A → RegularPrimeSet B L τ C D → RegularPrimeSet B L τ C V →
          (∏ p ∈ A, p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) →
          0 < j → j ≤ auxiliaryCutoff B → (j : ℝ) ≤ (B : ℝ)^2 →
          tiltedLargeHighPairCount B L k j d f τ C Δ A D V ≤
            K/(j : ℝ)*((A.card : ℝ)+1)*((D.card : ℝ)+1)*((V.card : ℝ)+1)*
              Real.exp ((largeMultiplicityBase+largeMultiplicityLoss Δ δ τ ε)*auxiliaryLogLength B) := by
  obtain ⟨τa,hτa,henv⟩ := omissionEnvelope_entropy hk hε
  obtain ⟨τb,hτb,hpre⟩ := regularPrefixChoices_entropy hk hε
  refine ⟨min τa (min τb 1),lt_min hτa (lt_min hτb (by norm_num)),?_⟩
  intro τ hτ hτsmall
  have hτa' : τ ≤ τa := hτsmall.trans (min_le_left _ _)
  have hτb' : τ ≤ τb := (hτsmall.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hτ1 : τ ≤ 1 := (hτsmall.trans (min_le_right _ _)).trans (min_le_right _ _)
  obtain ⟨K,hK,hactive⟩ := active_high_addition_class_bound hFord hM hk hkg hg hg1 hΔ hgap hδ hδ1 hτ.le hτ1 hε
  refine ⟨K,hK,?_⟩
  filter_upwards [hactive,auxiliaryLogLength_tendsto.eventually_gt_atTop 0] with B hB hℓ
  intro C A D V j d f hA hD hV hAr hDr hVr hAsize hj hcut hjB
  let ℓ := auxiliaryLogLength B
  let E := omissionEnvelope B L k τ A d
  let F := omissionEnvelope B L k τ D f
  let P := regularPrefixChoices B L k V f
  let S := K/(j : ℝ)*Real.exp (largeAvailabilityExponent g Δ δ τ ε ℓ d*ℓ)
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hpoint (Oa : Finset ℕ) (_hOa : Oa ∈ E) (Od : Finset ℕ) (_hOd : Od ∈ F)
      (Y : Finset ℕ) (hY : Y ∈ P) :
      tiltedRegularSubsetCount B L τ C A (activeHighAdditionClass B L k τ C Δ A
        (∏ p ∈ A \ Oa, p) j ((∏ p ∈ D \ Od, p)*(∏ p ∈ Y, p)) d) ≤ S := by
    have hYsub : Y ⊆ auxiliaryPrimes B := by
      have hy := mem_powerset.mp (mem_filter.mp hY).1
      have hp : primePrefix B ((k : ℝ)/L) V ⊆ V := by
        unfold primePrefix
        split_ifs
        · exact filter_subset _ _
        · exact subset_rfl
      exact (hy.trans hp).trans hV
    have he0 : 0 < (∏ p ∈ A \ Oa, p : ℕ) :=
      prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hA (mem_sdiff.mp hp).1)).pos)
    have hb0 : 0 < (∏ p ∈ D \ Od, p : ℕ)*(∏ p ∈ Y, p) := mul_pos
      (prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hD (mem_sdiff.mp hp).1)).pos))
      (prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hYsub hp)).pos))
    have heA : (∏ p ∈ A \ Oa, p : ℕ) ≤ ∏ p ∈ A, p :=
      Nat.le_of_dvd (prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hA hp)).pos))
        (prod_dvd_prod_of_subset _ _ id sdiff_subset)
    exact hB C A _ j _ d hA hAsize he0 hb0 hj hcut
      (auxiliary_product_coprime_lag (sdiff_subset.trans hA) hj hcut)
      ((show ((∏ p ∈ A \ Oa, p : ℕ) : ℝ) ≤ (∏ p ∈ A, p : ℕ) by exact_mod_cast heA).trans hAsize) hjB
  have hcount := tiltedLargeHighPairCount_le_classes A D V hk hτ.le hℓ hA hAr hDr hVr
    (j := j) (d := d) (f := f) (Δ := Δ)
  have hcounts : tiltedLargeHighPairCount B L k j d f τ C Δ A D V ≤
      (E.card : ℝ)*F.card*P.card*S := by
    refine hcount.trans ?_
    calc
      _ ≤ ∑ Oa ∈ E, ∑ Od ∈ F, ∑ Y ∈ P, S := by
        apply sum_le_sum
        intro Oa hOa
        apply sum_le_sum
        intro Od hOd
        exact sum_le_sum (fun Y hY => hpoint Oa hOa Od hOd Y hY)
      _ = _ := by simp only [sum_const,nsmul_eq_mul]; ring
  let ea := (g/2)*Real.binEntropy (2*min ((d : ℝ)/(g*ℓ)) (1/2))+ε+highOmissionExponent τ
  let eb := (g/2)*Real.binEntropy (2*min ((f : ℝ)/(g*ℓ)) (1/2))+ε+highOmissionExponent τ
  let ec := (g/2)*Real.binEntropy (2*min ((f : ℝ)/(g*ℓ)) (1/2))+ε
  have hca : (E.card : ℝ) ≤ ((A.card : ℝ)+1)*Real.exp (ea*ℓ) := by
    have hh := henv τ hτ hτa' B C A d hℓ hAr
    rwa [hkg] at hh
  have hcb : (F.card : ℝ) ≤ ((D.card : ℝ)+1)*Real.exp (eb*ℓ) := by
    have hh := henv τ hτ hτa' B C D f hℓ hDr
    rwa [hkg] at hh
  have hcc : (P.card : ℝ) ≤ ((V.card : ℝ)+1)*Real.exp (ec*ℓ) := by
    have hh := hpre τ hτ.le hτb' B C V f hℓ hVr
    rwa [hkg] at hh
  have hexp := large_multiplicity_exponent_bound (Δ := Δ) (τ := τ) (ε := ε)
    (ℓ := ℓ) (d := d) (f := f) hg.le hg1 hδ.le
  have hprod := mul_le_mul (mul_le_mul hca hcb (Nat.cast_nonneg _)
    (mul_nonneg (by positivity) (Real.exp_pos _).le)) hcc (Nat.cast_nonneg _)
      (mul_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le)
        (mul_nonneg (by positivity) (Real.exp_pos _).le))
  refine hcounts.trans ((mul_le_mul_of_nonneg_right hprod hS).trans ?_)
  have heq : Real.exp (ea*ℓ)*Real.exp (eb*ℓ)*Real.exp (ec*ℓ)*
      Real.exp (largeAvailabilityExponent g Δ δ τ ε ℓ d*ℓ) =
      Real.exp ((largeAvailabilityExponent g Δ δ τ ε ℓ d+ea+eb+ec)*ℓ) := by
    rw [← Real.exp_add,← Real.exp_add,← Real.exp_add]
    congr 1
    ring
  calc
    _ = K/(j : ℝ)*((A.card : ℝ)+1)*((D.card : ℝ)+1)*((V.card : ℝ)+1)*
        (Real.exp (ea*ℓ)*Real.exp (eb*ℓ)*Real.exp (ec*ℓ)*
          Real.exp (largeAvailabilityExponent g Δ δ τ ε ℓ d*ℓ)) := by dsimp only [S]; ring
    _ = K/(j : ℝ)*((A.card : ℝ)+1)*((D.card : ℝ)+1)*((V.card : ℝ)+1)*
        Real.exp ((largeAvailabilityExponent g Δ δ τ ε ℓ d+ea+eb+ec)*ℓ) := by rw [heq]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right hexp hℓ.le

end JointDickman

end OAI
