import OAI.NumberTheory.TwoPoint.Bounds.ActualPaddingMarginal

namespace OAI

/-! Loss of padding mass from the actual graph density and degree
cutoffs.  The second moment is applied before discarding the large bins. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

lemma FiniteLaw.weighted_large_bin_cut {A I : Type*} [Fintype A]
    (μ : FiniteLaw A) (bins : Finset I) (weight : A → ℝ)
    (hw : ∀ a, 0 ≤ weight a) (ρ : A → I → ℝ)
    (hρ : ∀ a j, 0 ≤ ρ a j) (K L : ℝ) (hK : 0 < K) (hL : 0 < L) :
    μ.average (fun a => weight a *
      ∑ j ∈ bins, if K / L < ρ a j then ρ a j else 0) ≤
      (L / K) * μ.average (fun a => weight a * ∑ j ∈ bins, (ρ a j) ^ 2) := by
  calc
    _ ≤ μ.average (fun a => weight a *
        ∑ j ∈ bins, (L / K) * (ρ a j) ^ 2) := by
      apply μ.average_mono
      intro a
      apply mul_le_mul_of_nonneg_left _ (hw a)
      exact sum_le_sum (fun j _ => large_nonnegative_value (ρ a j) K L (hρ a j) hK hL)
    _ = _ := by
      simp only [← mul_sum, FiniteLaw.average]
      rw [mul_sum]
      apply sum_congr rfl
      intro a _
      ring

theorem ModFiveThetaInput.actual_family_padding_large_bin_cut (hP : ModFiveThetaInput)
    (E : Finset ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L η c K : ℝ) (h J M B : ℕ)
      (data : ProhibitedPrimeFamily h J M), data.Q = paddingPrimeSupply E L →
      ∀ (site : ℤ) (bins : Finset ℤ), 1 ≤ L → 0 < η → η ≤ 1 → 0 < K →
      ∀ (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
        (D : Finset ℕ), D ⊆ retainedPrimeDivisors data.Q →
      (data.residueLaw B hB).average (fun x =>
        (actualPaddingVertex data.Q (data.residueOrigin x + site)) ^ 2 *
          ∑ j ∈ bins, if K / L < paddingDensity D actualPaddingCoefficient
            (actualPaddingBin η c j) (actualPaddingVertex data.Q) (data.residueOrigin x + site)
            then paddingDensity D actualPaddingCoefficient (actualPaddingBin η c j)
              (actualPaddingVertex data.Q) (data.residueOrigin x + site) else 0) /
                paddingTiltNormalizer data.Q ≤ C / K := by
  obtain ⟨C, hC, hb⟩ := hP.actual_family_padding_bin_square E
  refine ⟨C, hC, ?_⟩
  intro L η c K h J M B data hQ site bins hL hη hηone hK hB D hD
  have hLp : 0 < L := zero_lt_one.trans_le hL
  let μ := data.residueLaw B hB
  let ρ := fun (x : ↥(data.P ∪ data.Q) → Fin B) j => paddingDensity D actualPaddingCoefficient (actualPaddingBin η c j)
    (actualPaddingVertex data.Q) (data.residueOrigin x + site)
  let w := fun (x : ↥(data.P ∪ data.Q) → Fin B) => (actualPaddingVertex data.Q (data.residueOrigin x + site)) ^ 2
  have hs := μ.weighted_large_bin_cut bins w (fun x => sq_nonneg _) ρ
    (fun x j => actualPaddingDensity_nonneg data.Q D _ _) K L hK hLp
  calc
    _ ≤ ((L / K) * μ.average (fun x => w x * ∑ j ∈ bins, (ρ x j) ^ 2)) /
        paddingTiltNormalizer data.Q :=
      div_le_div_of_nonneg_right hs (paddingTiltNormalizer_pos data.Q).le
    _ = (L / K) * (μ.average (fun x => w x * ∑ j ∈ bins, (ρ x j) ^ 2) /
        paddingTiltNormalizer data.Q) := by ring
    _ ≤ (L / K) * (C / L) := mul_le_mul_of_nonneg_left
      (hb L η c h J M B data hQ site bins hL hη hηone hB D hD)
      (div_nonneg hLp.le hK.le)
    _ = C / K := by field_simp

/-- The bin densities form a subprobability distribution even after
restricting the available padding divisors. -/
lemma actualPaddingDensity_sum_le_one (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (D : Finset ℕ)
    (hD : D ⊆ retainedPrimeDivisors Q) (n : ℤ)
    (η c : ℝ) (hη : 0 < η) (bins : Finset ℤ) :
    (∑ j ∈ bins, paddingDensity D actualPaddingCoefficient (actualPaddingBin η c j)
      (actualPaddingVertex Q) n) ≤ 1 := by
  unfold paddingDensity
  rw [← sum_div, sum_comm, actualPaddingVertex_sq]
  apply (div_le_one (zero_lt_one.trans_le (actualPaddingWeight_one_le Q n))).mpr
  calc
    _ ≤ ∑ q ∈ D, if (q : ℤ) ∣ n then actualPaddingCoefficient q else 0 := by
      apply sum_le_sum
      intro q _
      have he (j : ℤ) : actualPaddingBin η c j q ↔ paddingBin η c (Real.log q) = j :=
        (paddingBin_eq_iff η c (Real.log q) j hη).symm
      simp only [he]
      by_cases hd : (q : ℤ) ∣ n
      · simp only [hd, and_true]
        simp only [sum_ite_eq]
        split_ifs
        · exact le_rfl
        · exact actualPaddingCoefficient_nonneg q
      · simp only [hd, and_false, ite_false, sum_const_zero, le_refl]
    _ ≤ ∑ q ∈ retainedPrimeDivisors Q,
        if (q : ℤ) ∣ n then actualPaddingCoefficient q else 0 := by
      apply sum_le_sum_of_subset_of_nonneg hD
      intro q _ _
      split_ifs
      · exact actualPaddingCoefficient_nonneg q
      · exact le_rfl
    _ = _ := (actualPaddingWeight_eq_divisor_sum Q hQ n).symm

lemma actualPadding_keep_loss (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : Finset ℕ) (hD : D ⊆ retainedPrimeDivisors Q) (n : ℤ)
    (L K η c : ℝ) (hη : 0 < η) (bins : Finset ℤ) :
    (∑ j ∈ bins, if ¬integerEdgeKeep D actualPaddingCoefficient (actualPaddingBin η c j)
      (actualPaddingVertex Q) L K (actualPaddingDegreeCut Q L) n then
        paddingDensity D actualPaddingCoefficient (actualPaddingBin η c j)
          (actualPaddingVertex Q) n else 0) ≤
      (∑ j ∈ bins, if K / L < paddingDensity D actualPaddingCoefficient
        (actualPaddingBin η c j) (actualPaddingVertex Q) n then
          paddingDensity D actualPaddingCoefficient (actualPaddingBin η c j)
            (actualPaddingVertex Q) n else 0) +
        if ¬actualPaddingDegreeCut Q L n then 1 else 0 := by
  by_cases hc : actualPaddingDegreeCut Q L n
  · simp only [integerEdgeKeep, hc, and_true, not_le, not_true_eq_false,
      ite_false, add_zero, le_refl]
  · have hs := actualPaddingDensity_sum_le_one Q hQ D hD n η c hη bins
    have hp : 0 ≤ ∑ j ∈ bins, if K / L < paddingDensity D actualPaddingCoefficient
        (actualPaddingBin η c j) (actualPaddingVertex Q) n then
          paddingDensity D actualPaddingCoefficient (actualPaddingBin η c j)
            (actualPaddingVertex Q) n else 0 := by
      apply sum_nonneg
      intro j _
      split_ifs
      · exact actualPaddingDensity_nonneg Q D _ n
      · exact le_rfl
    simp only [integerEdgeKeep, hc, and_false, not_false_eq_true, ite_true]
    linarith

/-- Both literal vertex cutoffs together remove only `O(1/K) + L⁻¹⁰⁰`
of the normalized, padding-weighted mass, summed over all selected bins. -/
theorem ModFiveThetaInput.eventually_actual_padding_keep_loss
    (hP : ModFiveThetaInput) (E : Finset ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (η c K : ℝ) (h J M B : ℕ) (data : ProhibitedPrimeFamily h J M),
      data.Q = paddingPrimeSupply E L →
      ∀ (site : ℤ) (bins : Finset ℤ), 0 < η → η ≤ 1 → 0 < K →
      ∀ (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
        (D : Finset ℕ), D ⊆ retainedPrimeDivisors data.Q →
      (data.residueLaw B hB).average (fun x =>
        (actualPaddingVertex data.Q (data.residueOrigin x + site)) ^ 2 *
          ∑ j ∈ bins, if ¬integerEdgeKeep D actualPaddingCoefficient
            (actualPaddingBin η c j) (actualPaddingVertex data.Q) L K
            (actualPaddingDegreeCut data.Q L) (data.residueOrigin x + site) then
              paddingDensity D actualPaddingCoefficient (actualPaddingBin η c j)
                (actualPaddingVertex data.Q) (data.residueOrigin x + site) else 0) /
                  paddingTiltNormalizer data.Q ≤ C / K + L ^ (-100 : ℝ) := by
  obtain ⟨C, hC, hb⟩ := hP.actual_family_padding_large_bin_cut E
  refine ⟨C, hC, ?_⟩
  filter_upwards [hP.eventually_actual_family_padding_degree_tail E,
    eventually_ge_atTop (1 : ℝ)] with L ht hL
  intro η c K h J M B data hQ site bins hη hηone hK hB D hD
  let μ := data.residueLaw B hB
  let ρ := fun (x : ↥(data.P ∪ data.Q) → Fin B) j => paddingDensity D actualPaddingCoefficient (actualPaddingBin η c j)
    (actualPaddingVertex data.Q) (data.residueOrigin x + site)
  let w := fun (x : ↥(data.P ∪ data.Q) → Fin B) => (actualPaddingVertex data.Q (data.residueOrigin x + site)) ^ 2
  let bad := fun (x : ↥(data.P ∪ data.Q) → Fin B) => if ¬actualPaddingDegreeCut data.Q L
    (data.residueOrigin x + site) then (1 : ℝ) else 0
  have hp := fun (x : ↥(data.P ∪ data.Q) → Fin B) => actualPadding_keep_loss data.Q data.primeQ D hD
    (data.residueOrigin x + site) L K η c hη bins
  calc
    _ ≤ (μ.average (fun x => w x *
          ∑ j ∈ bins, if K / L < ρ x j then ρ x j else 0) +
        μ.average (fun x => w x * bad x)) / paddingTiltNormalizer data.Q := by
      apply div_le_div_of_nonneg_right _ (paddingTiltNormalizer_pos data.Q).le
      calc
        _ ≤ μ.average (fun x => w x *
            ((∑ j ∈ bins, if K / L < ρ x j then ρ x j else 0) + bad x)) := by
          apply μ.average_mono
          intro x
          exact mul_le_mul_of_nonneg_left (hp x) (sq_nonneg _)
        _ = _ := by simp only [FiniteLaw.average, mul_add, sum_add_distrib]
    _ = μ.average (fun x => w x *
          ∑ j ∈ bins, if K / L < ρ x j then ρ x j else 0) / paddingTiltNormalizer data.Q +
        μ.average (fun x => w x * bad x) / paddingTiltNormalizer data.Q := add_div _ _ _
    _ ≤ C / K + L ^ (-100 : ℝ) := add_le_add
      (hb L η c K h J M B data hQ site bins hL hη hηone hK hB D hD)
      (ht h J M B data hQ hB site)

end TwoPointCorrelations

end OAI
