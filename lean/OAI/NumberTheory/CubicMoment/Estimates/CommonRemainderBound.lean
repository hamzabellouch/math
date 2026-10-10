import OAI.NumberTheory.CubicMoment.Estimates.CommonOuterBound

namespace OAI

/-! Bound the noncoprime remainder by the energy of the genuine
common-factor blocks, and then by the original prime-convolution energy. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

 theorem primaryMass_sub_coprime_outer {ε B : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hB : 1 ≤ B) (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset Eisenstein) (u : Eisenstein → ℂ) (Q A L D : ℝ),
      1 ≤ Q → 0 < A → 1 ≤ L → 1 ≤ D →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ L ≤ norm a ∧ norm a ≤ B*L) →
      (∀ k ∈ commonRowFactors S, k ≠ 1 → D ≤ norm k) →
      ‖primarySmoothedSieveMass S u W (A/Q^2)-coprimeGramForm S u W (A/Q^2)‖ ≤
        commonOuterCost W C ε B Q A L D*
          ∑ k ∈ commonRowFactors S, (2:ℝ)^(primaryPrimeFactors k).card*commonBlockEnergy S u k := by
  obtain ⟨C,hC,hbound⟩ := commonGramBlock_outer_bound hε hε1 hB W hW hW'
  refine ⟨C,hC,?_⟩
  intro S u Q A L D hQ hA hL hD hS hrough
  have hQp : 0 < Q := zero_lt_one.trans_le hQ
  have hcost : 0 ≤ commonOuterCost W C ε B Q A L D :=
    commonOuterCost_nonneg W hC.le (zero_le_one.trans hB) hA.le (zero_le_one.trans hL)
  rw [primaryMass_sub_coprime_common S (fun a ha => ⟨(hS a ha).1,(hS a ha).2.1⟩)
    u W hW hW' (by positivity)]
  calc
    _ ≤ ∑ k ∈ (commonRowFactors S).filter (· ≠ 1), ‖commonGramBlock S u W (A/Q^2) k‖ :=
      norm_sum_le _ _
    _ ≤ ∑ k ∈ (commonRowFactors S).filter (· ≠ 1),
        (2:ℝ)^(primaryPrimeFactors k).card*commonOuterCost W C ε B Q A L D*commonBlockEnergy S u k := by
      apply Finset.sum_le_sum
      intro k hk
      exact hbound S u Q A L D hQ hA hL hD hS k (Finset.mem_filter.mp hk).1
        (hrough k (Finset.mem_filter.mp hk).1 (Finset.mem_filter.mp hk).2)
    _ = commonOuterCost W C ε B Q A L D*
        ∑ k ∈ (commonRowFactors S).filter (· ≠ 1),
          (2:ℝ)^(primaryPrimeFactors k).card*commonBlockEnergy S u k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) (fun k hk hk' => mul_nonneg (by positivity)
        (commonBlockEnergy_nonneg S u k))) hcost

 theorem fullPrime_divisor_noncoprime_outer {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ε R : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 1 ≤ R)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : ι → ℝ → ℂ) (X : ι → ℝ) (L D A : ℝ)
      (e d : Eisenstein) (β : Eisenstein → ℂ) (u : ℝ),
      (∀ i, 0 < X i) → (∏ i, X i) = L → 1 ≤ L → 1 ≤ D → 0 < A → primary d →
      (∀ i x, x < 1 → W i x = 0) → (∀ i x, R < x → W i x = 0) →
      (∀ i, D < X i) →
      ‖divisorDispersionVariance d (fullSquarefreePrimeSupport R W X e) β u V A-
        divisorCoprimeDispersionGram d (fullSquarefreePrimeSupport R W X e) β u V A‖ ≤
      commonOuterCost V C ε (R^Fintype.card ι) (norm d) A L D*
        (2:ℝ)^(3*Fintype.card ι)*
          ∑ a ∈ fullSquarefreePrimeSupport R W X e, ‖β a‖^2 := by
  obtain ⟨C,hC,hbound⟩ := primaryMass_sub_coprime_outer hε hε1
    (one_le_pow₀ hR) V hV hV'
  refine ⟨C,hC,?_⟩
  intro W X L D A e d β u hX hprod hL hD hA hd hlo hhi hrough
  let S := fullSquarefreePrimeSupport R W X e
  let v := divisorGramCoefficient d β u
  have hS : ∀ a ∈ S, primary a ∧ Squarefree a :=
    fun a ha => fullSquarefreePrimeSupport_primary R W X e ha
  have hSN : ∀ a ∈ S, primary a ∧ Squarefree a ∧ L ≤ norm a ∧ norm a ≤ R^Fintype.card ι*L := by
    intro a ha
    have hn := fullPrimeProduct_norm_bounds R W X hX hlo hhi (Finset.mem_filter.mp ha).1
    rw [hprod] at hn
    exact ⟨(hS a ha).1,(hS a ha).2,hn⟩
  have hh := hbound S v (norm d) A L D (one_le_norm (primary_ne_zero hd)) hA hL hD hSN
    (fun k hk hk1 => (fullPrime_nonunit_common_factor_large W X hX hlo hhi hrough e hk hk1).le)
  rw [divisorDispersionVariance_eq_primaryMass hd S (fun a ha => (hS a ha).1) β u V hV hV' hA,
    divisorCoprimeDispersionGram_eq_coprimeGram]
  apply hh.trans
  have he := fullPrime_common_energy_bound R W X e v
  have he' : (∑ a ∈ S, ‖v a‖^2) ≤ ∑ a ∈ S, ‖β a‖^2 := by
    apply Finset.sum_le_sum
    intro a ha
    exact pow_le_pow_left₀ (_root_.norm_nonneg _)
      (divisorGramCoefficient_norm_le d β u (hS a ha).1) 2
  have henergy := he.trans (mul_le_mul_of_nonneg_left he' (by positivity))
  exact (mul_le_mul_of_nonneg_left henergy
    (commonOuterCost_nonneg V hC.le (by positivity) hA.le (zero_le_one.trans hL))).trans_eq (by ring)

end CubicFirstMoment

end

end OAI
