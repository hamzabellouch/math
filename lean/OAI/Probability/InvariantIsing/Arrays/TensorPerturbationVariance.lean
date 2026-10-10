import OAI.Probability.InvariantIsing.Arrays.NSpinTensorHaarFluctuation
import OAI.Probability.InvariantIsing.Arrays.TensorPerturbationComparison

namespace OAI

/-! The full O(1/N) pressure variance for the manuscript's finite perturbation. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma monomialVarianceIncrement_zero_le_one (n r : ℕ) :
    (varianceIncrement (monomialPath n r) 0 : ℝ) ≤ 1 := by
  rw [varianceIncrement_coe (monomialPath_monotone n r) (monomialPath_nonneg n r 0)]
  change monomialPath n r 0 ≤ 1
  exact ((monomialPath_monotone n r) (Nat.zero_le n)).trans (monomialPath_diag_le_one n r)

/-- With bounded field heights and linearly enumerated monomial degrees,
the actual finite perturbation has a uniform pressure variance of order
inverse volume. The only conditional inputs are the named Haar and Gaussian
concentration consequences. -/
theorem tensorPerturbationPressure_variance (hhaar : HaarConcentrationInput)
    (hgauss : GaussianLipschitzVarianceInput) :
    ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, 3 ≤ N →
    ∀ μ : Measure (SpecialOrthogonal N), IsProbabilityMeasure μ → μ.IsMulLeftInvariant →
    ∀ m : ℕ, ∀ eig c : Fin N → ℝ, ∀ K : ℝ, 0 < K → (∀ i, |eig i| ≤ K) →
    ∀ I : Fin m → Finset (Fin N), ∀ degree : Fin N → Fin m → ℕ,
    ∀ u : Fin N → ℝ, (∀ j, |u j| ≤ 2) →
    ∀ D : ℝ, 0 ≤ D → (∀ j, (∑ a, (degree j a : ℝ)) ≤ D * ((j : ℝ) + 1)) →
    ∀ n : ℕ, ∀ treeDegree : Fin N → ℕ, ∀ b : ℕ → ℝ, CascadeExponents n b →
    ∀ h : ℕ → ℝ, Monotone h → 0 ≤ h 0 → ∀ H : ℝ, h n ≤ H →
      let v := tensorPathProfile I degree n treeDegree h
      let P := tensorRootTreeLaw I degree n b (fun i => v (i + 1)) (v 0)
      let F := tensorDisorderPressure eig c I degree (tensorPerturbationAmplitude N u) n
      MemLp F 2 (μ.prod P) ∧ variance F (μ.prod P) ≤
        (4 * (∫ T, (Real.log (rawTreeTotal n T).toReal) ^ 2
          ∂(rawCascadeLaw n b : Measure (RawTree n))) + H + 4 + C * (K + 8 * D) ^ 2) / N := by
  obtain ⟨C, hC, hvar⟩ := tensorDisorderPressure_variance hhaar hgauss
  refine ⟨C, hC, ?_⟩
  intro N hN μ hμ hμinv m eig c K hK heig I degree u hu D hD hdegree n treeDegree b hb
    h hh h0 H hH v P F
  let a := tensorPerturbationAmplitude N u
  let s := varianceIncrement h
  let q := fun i j => varianceIncrement (monomialPath n (treeDegree j)) i
  let B := 4 * (∫ T, (Real.log (rawTreeTotal n T).toReal) ^ 2
    ∂(rawCascadeLaw n b : Measure (RawTree n)))
  let L := K + 2 * (N : ℝ)⁻¹ *
    (∑ i : Fin (n + 1), ∑ j, (q i j : ℝ) * a j ^ 2 * ∑ a, (degree j a : ℝ))
  have hNm : 0 < N := by omega
  have hn : (0 : ℝ) < N := by exact_mod_cast hNm
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.succ_le_of_lt hNm)
  have hv := hvar N hN μ hμ hμinv m N eig c K hK heig I degree a n b hb s q
  refine ⟨hv.1, hv.2.trans ?_⟩
  have hB : 0 ≤ B := mul_nonneg (by norm_num)
    (integral_nonneg fun _ => sq_nonneg _)
  have hsite : (s 0 : ℝ) ≤ H := by
    rw [varianceIncrement_coe hh h0]
    exact (hh (Nat.zero_le n)).trans hH
  have hsum : (∑ j, (q 0 j : ℝ) * a j ^ 2) ≤ 4 * N := by
    calc
      _ ≤ ∑ j, a j ^ 2 := Finset.sum_le_sum fun j _ => by
        exact (mul_le_mul_of_nonneg_right (monomialVarianceIncrement_zero_le_one n (treeDegree j))
          (sq_nonneg _)).trans_eq (one_mul _)
      _ ≤ 4 * N * perturbationScale N ^ 2 := tensorPerturbationAmplitude_square_sum_le N u hu
      _ ≤ 4 * N := (mul_le_mul_of_nonneg_left (perturbationScale_sq_le_one hNm)
        (show 0 ≤ 4 * (N : ℝ) by positivity)).trans_eq (mul_one _)
  have hroot : B + (s 0 : ℝ) * N + ∑ j, (q 0 j : ℝ) * a j ^ 2 ≤ B + (H + 4) * N := by
    have hs := mul_le_mul_of_nonneg_right hsite hn.le
    linarith
  have hrootnorm : (B + (s 0 : ℝ) * N + ∑ j, (q 0 j : ℝ) * a j ^ 2) / (N : ℝ) ^ 2 ≤
      (B + H + 4) / N := by
    calc
      _ ≤ (B + (H + 4) * N) / (N : ℝ) ^ 2 := div_le_div_of_nonneg_right hroot (sq_nonneg _)
      _ = B / (N : ℝ) ^ 2 + (H + 4) / N := by field_simp
      _ ≤ B / N + (H + 4) / N := add_le_add
        (div_le_div_of_nonneg_left hB hn (by nlinarith : (N : ℝ) ≤ (N : ℝ) ^ 2)) (le_refl _)
      _ = _ := by ring
  have hdegreeSum := (tensorPathProfile_rotation_cap degree a n treeDegree).trans
    (tensorPerturbationAmplitude_degree_sum_le u hu degree D hD hdegree)
  have hnorm := mul_le_mul_of_nonneg_left hdegreeSum
    (show 0 ≤ 2 * (N : ℝ)⁻¹ by positivity)
  have hid : 2 * (N : ℝ)⁻¹ * (4 * N * perturbationScale N ^ 2 * D) =
      8 * perturbationScale N ^ 2 * D := by field_simp; ring
  rw [hid] at hnorm
  have hsmall := mul_le_mul_of_nonneg_right (perturbationScale_sq_le_one hNm)
    (show 0 ≤ 8 * D by positivity)
  have hL : L ≤ K + 8 * D := by dsimp only [L]; nlinarith
  have hL0 : 0 ≤ L := by dsimp only [L, q]; positivity
  have hsq : L ^ 2 ≤ (K + 8 * D) ^ 2 := pow_le_pow_left₀ hL0 hL 2
  have hHaar : C * L ^ 2 / N ≤ C * (K + 8 * D) ^ 2 / N :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hC.le) hn.le
  exact (add_le_add hrootnorm hHaar).trans_eq (by dsimp only [B]; ring)

end InvariantIsing

end

end OAI
