import OAI.NumberTheory.JointDickman.Analysis.MellinBoundedFrequencyLimit
import OAI.NumberTheory.JointDickman.Amplification.BinWeightedMarginal
import OAI.NumberTheory.JointDickman.Arithmetic.FiniteBinDistributionDischarge

namespace OAI

/-! # Unconditional low-frequency control of the actual weighted bin labels -/
namespace JointDickman
open Finset Filter
open scoped Topology

lemma norm_binLabel_le_one_of_norm_le {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (z : ι → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) (n : ℕ) :
    ‖binLabel E z n‖ ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [binLabel_apply hn, norm_prod]
    apply Finset.prod_le_one₀
    · intro i _
      exact norm_nonneg _
    · intro i _
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (hz i)

lemma binDistributionMean_norm_le_one_of_norm_le {J : ℕ}
    (ν : BinCountState J → ℝ) (hν : ∀ r, 0 ≤ ν r) (hνone : ∑ r, ν r = 1)
    (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖ ≤ 1) :
    ‖binDistributionMean ν ζ‖ ≤ 1 := by
  unfold binDistributionMean
  calc
    _ ≤ ∑ r : BinCountState J, ‖(ν r : ℂ) * ∏ i, ζ i ^ (r i).val‖ := norm_sum_le _ _
    _ ≤ ∑ r : BinCountState J, ν r := by
      apply sum_le_sum
      intro r _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hν r)]
      apply mul_le_of_le_one_right (hν r)
      rw [norm_prod]
      apply Finset.prod_le_one₀
      · intro i _
        exact norm_nonneg _
      · intro i _
        rw [norm_pow]
        exact pow_le_one₀ (norm_nonneg _) (hζ i)
    _ = 1 := hνone

noncomputable def centeredWeightedBinCoefficient (J : ℕ) (ζ : Fin (J-1) → ℂ)
    (μ : ℂ) (P : Finset ℕ) (t : ℕ → ℝ) (x : ℝ) : ArithmeticFunction ℂ :=
  ⟨fun n => (binLabel (fun i : Fin (J-1) => primeBin x J (i.val+1)) ζ n - μ) *
    (finitePrimeWeight P t n : ℂ), by simp⟩

lemma centeredWeightedBinCoefficient_norm {J : ℕ} (ζ : Fin (J-1) → ℂ)
    (hζ : ∀ i, ‖ζ i‖ ≤ 1) {μ : ℂ} (hμ : ‖μ‖ ≤ 1)
    {P : Finset ℕ} (t : ℕ → ℝ) (ht : ∀ p ∈ P, 0 ≤ t p ∧ t p ≤ 1)
    (x : ℝ) (n : ℕ) : ‖centeredWeightedBinCoefficient J ζ μ P t x n‖ ≤ 2 := by
  change ‖(binLabel _ ζ n - μ) * (finitePrimeWeight P t n : ℂ)‖ ≤ 2
  have hl : ‖binLabel (fun i : Fin (J-1) => primeBin x J (i.val+1)) ζ n - μ‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by linarith [norm_binLabel_le_one_of_norm_le (fun i : Fin (J-1) => primeBin x J (i.val+1)) ζ hζ n])
  have hw : ‖(finitePrimeWeight P t n : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (finitePrimeWeight_bounds ht n).1]
    exact (finitePrimeWeight_bounds ht n).2
  rw [norm_mul]
  exact (mul_le_mul hl hw (norm_nonneg _) (by norm_num)).trans_eq (mul_one 2)

/-- The one-variable bin law, already proved in this development, suffices
for every bounded angular-frequency interval. The mean is independent of
all subsequent finite-prime restrictions. -/
theorem weightedBin_low_frequency {J : ℕ} (hJ : 2 ≤ J)
    (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖ ≤ 1) :
    ∃ μ : ℂ, ‖μ‖ ≤ 1 ∧ ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime) →
      ∀ t : ℕ → ℝ, (∀ p ∈ P, 0 ≤ t p ∧ t p ≤ 1) →
      ∀ A T ε : ℝ, 0 < A → 0 ≤ T → 0 < ε →
      ∀ᶠ x : ℝ in atTop, ∀ τ : ℝ, |τ| ≤ T →
        ‖angularMellinPolynomial (Ioc ⌊A * x⌋₊ ⌊4 * (A * x)⌋₊)
          (centeredWeightedBinCoefficient J ζ μ P t x) τ‖ ≤ ε := by
  obtain ⟨ν, hν, hνone, hνmean, _⟩ := finiteBinDistributionInput J hJ
  let μ := binDistributionMean ν ζ
  have hμ : ‖μ‖ ≤ 1 := binDistributionMean_norm_le_one_of_norm_le ν hν hνone ζ hζ
  have hmean : ∀ A : ℝ, 0 < A → Tendsto (centeredBinPrefix J ζ μ A) atTop (𝓝 0) :=
    fun A hA => centeredBinPrefix_tendsto (by omega) ν hνmean ζ hA
  refine ⟨μ, hμ, ?_⟩
  intro P hP t ht A T ε hA hT hε
  apply angularMellin_uniform_bounded_frequency
    (fun x n => centeredWeightedBinCoefficient J ζ μ P t x n) (by norm_num : (0 : ℝ) ≤ 2)
    (centeredWeightedBinCoefficient_norm ζ hζ hμ t ht)
    (fun x => (centeredWeightedBinCoefficient J ζ μ P t x).map_zero) ?_ hA hT hε
  intro B hB
  have hh := (weightedCenteredBinPrefix_tendsto (by omega) ζ μ hmean hP t hB).const_mul (B : ℂ)
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  dsimp only [weightedCenteredBinPrefix, centeredWeightedBinCoefficient, ArithmeticFunction.coe_mk]
  have hBc : (B : ℂ) ≠ 0 := by exact_mod_cast hB.ne'
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  field_simp

end JointDickman

end OAI
