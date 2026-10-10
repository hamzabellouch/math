import OAI.NumberTheory.TwoPoint.Bounds.PaddingResidueTilt

namespace OAI

/-! The squared-bin estimate gives the exact `O(1/K)` cost of deleting
bins whose padding density exceeds `K/L`. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma large_nonnegative_value (r K L : ℝ) (hr : 0 ≤ r) (hK : 0 < K) (hL : 0 < L) :
    (if K / L < r then r else 0) ≤ (L / K) * r ^ 2 := by
  by_cases h : K / L < r
  · rw [ite_eq_left h, div_mul_eq_mul_div]
    apply (le_div_iff₀ hK).mpr
    have hh := (div_lt_iff₀ hL).mp h
    nlinarith [mul_nonneg hr (sub_nonneg.mpr hh.le)]
  · rw [ite_eq_right h]
    positivity

lemma FiniteLaw.large_bin_cut {A I : Type*} [Fintype A]
    (μ : FiniteLaw A) (bins : Finset I) (ρ : A → I → ℝ)
    (hρ : ∀ a j, 0 ≤ ρ a j) (K L : ℝ) (hK : 0 < K) (hL : 0 < L) :
    μ.average (fun a => ∑ j ∈ bins, if K / L < ρ a j then ρ a j else 0) ≤
      (L / K) * μ.average (fun a => ∑ j ∈ bins, (ρ a j) ^ 2) := by
  calc
    _ ≤ μ.average (fun a => ∑ j ∈ bins, (L / K) * (ρ a j) ^ 2) := by
      apply μ.average_mono
      intro a
      exact sum_le_sum (fun j _ => large_nonnegative_value (ρ a j) K L (hρ a j) hK hL)
    _ = _ := by
      simp only [← mul_sum, FiniteLaw.average]
      conv_rhs => rw [mul_sum]
      apply sum_congr rfl
      intro a _
      ring

lemma paddingBinMass_nonneg (Q : Finset ℕ) (a : Q → Bool) (η c : ℝ) (j : ℤ) :
    0 ≤ paddingBinMass Q a η c j := FiniteLaw.probability_nonneg _ _

/-- Uniform over bin translations and every finite collection of bins. -/
theorem ModFiveThetaInput.padding_large_bin_cut (hP : ModFiveThetaInput) (E : Finset ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L η c K : ℝ) (bins : Finset ℤ),
      1 ≤ L → 0 < η → η ≤ 1 → 0 < K →
      (paddingAvailableLaw (paddingPrimeSupply E L)
        (fun _ hp => (paddingPrimeSupply_prime hp).two_le)).average (fun a =>
          ∑ j ∈ bins, if K / L < paddingBinMass (paddingPrimeSupply E L) a η c j
          then paddingBinMass (paddingPrimeSupply E L) a η c j else 0) ≤ C / K := by
  obtain ⟨C, hC, hbound⟩ := hP.padding_bin_square E
  refine ⟨C, hC, fun L η c K bins hL hη hη1 hK => ?_⟩
  have hLp : 0 < L := zero_lt_one.trans_le hL
  calc
    _ ≤ (L / K) * (paddingAvailableLaw (paddingPrimeSupply E L)
        (fun _ hp => (paddingPrimeSupply_prime hp).two_le)).average
          (fun a => ∑ j ∈ bins, (paddingBinMass (paddingPrimeSupply E L) a η c j) ^ 2) :=
      FiniteLaw.large_bin_cut _ bins _ (fun a j => paddingBinMass_nonneg _ a η c j) K L hK hLp
    _ ≤ (L / K) * (C / L) :=
      mul_le_mul_of_nonneg_left (hbound L η c bins hL hη hη1) (div_nonneg hLp.le hK.le)
    _ = C / K := by field_simp

/-- The same bound in the original weighted uniform-residue expectation. -/
theorem ModFiveThetaInput.padding_residue_large_bin_cut (hP : ModFiveThetaInput)
    (E : Finset ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L η c K : ℝ) (B : ℕ) (n : ℤ) (bins : Finset ℤ),
      1 ≤ L → 0 < η → η ≤ 1 → 0 < K →
      ∀ hQB : ∀ p ∈ paddingPrimeSupply E L, p ≤ B,
      (FiniteLaw.independent (fun p : paddingPrimeSupply E L =>
        uniformResidueLaw B p.val (paddingPrimeSupply_prime p.property).pos
          (hQB p p.property))).average (fun z =>
            paddingTiltWeight _ (paddingResidueAvailable _ B n z) *
              ∑ j ∈ bins,
                if K / L < literalPaddingBinMass _ (paddingResidueAvailable _ B n z) η c j
                then literalPaddingBinMass _ (paddingResidueAvailable _ B n z) η c j else 0) /
                  paddingTiltNormalizer (paddingPrimeSupply E L) ≤ C / K := by
  obtain ⟨C, hC, hbound⟩ := hP.padding_large_bin_cut E
  refine ⟨C, hC, fun L η c K B n bins hL hη hη1 hK hQB => ?_⟩
  simp_rw [← paddingBinMass_eq_literal _ (fun p hp => paddingPrimeSupply_prime hp)]
  rw [padding_residue_tilt (paddingPrimeSupply E L) B
    (fun _ hp => (paddingPrimeSupply_prime hp).two_le) hQB n
    (fun a => ∑ j ∈ bins, if K / L < paddingBinMass _ a η c j then paddingBinMass _ a η c j else 0)]
  exact hbound L η c K bins hL hη hη1 hK

end TwoPointCorrelations

end OAI
