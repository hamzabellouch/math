import OAI.NumberTheory.JointDickman.Probability.CandidateSiteKernel

namespace OAI

/-! # The five-weight bound for one latent representation -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem candidateMeanWeight_small
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {L : ℕ} (hL : 1 ≤ L) {τ : ℝ} (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (M : ℕ) (S : Fin M → Finset ℕ)
      (χ : BlockCandidateIndex M → ℝ), (∀ e, χ e ≤ 1) →
      ∀ e, candidateMeanWeight B L τ C S χ e ≤ (B : ℝ)^(-(22/100 : ℝ)) := by
  let ε := (1-5*weightExponent τ-(22/100 : ℝ))/12
  have hm := (weight_margins_of_le_samplingTau hτsmall).2.2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hexp : 5*(weightExponent τ+ε)+ε-1 ≤ -(22/100 : ℝ) := by
    dsimp [ε]
    linarith
  obtain ⟨K,hK,hroot⟩ := independentRootMean_bounded hM
  have hgrow := ((tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop K
  filter_upwards [regular_weights_cap hL hτ hε,hroot,hgrow,eventually_gt_atTop 1]
    with B hcap hroot hgrow hB
  intro C M S χ hχ e
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  let Q := (B : ℝ)^(weightExponent τ+ε)
  have hQ : 0 ≤ Q := Real.rpow_nonneg (Nat.cast_nonneg B) _
  have hpair (n : ℕ) (R : Finset ℕ) :
      regularCoefficientWeight B L τ C n*regularResidueWeight B L τ C R ≤ Q*Q :=
    mul_le_mul ((hcap C).2 n) ((hcap C).1 R)
      (regularResidueWeight_nonneg B L τ C R) hQ
  let W := regularCoefficientWeight B L τ C (candidateLow e)*
      regularResidueWeight B L τ C (S e.1.1 \ e.2.1)*
      (regularCoefficientWeight B L τ C (candidateHigh e)*
        regularResidueWeight B L τ C (S e.1.2 \ e.2.2))*
      regularCoefficientWeight B L τ C (candidateQuotient e)
  have hW : 0 ≤ W := by
    dsimp [W]
    exact mul_nonneg (mul_nonneg
      (mul_nonneg (regularCoefficientWeight_nonneg _ _ _ _ _) (regularResidueWeight_nonneg _ _ _ _ _))
      (mul_nonneg (regularCoefficientWeight_nonneg _ _ _ _ _) (regularResidueWeight_nonneg _ _ _ _ _)))
      (regularCoefficientWeight_nonneg _ _ _ _ _)
  have hcapW : W ≤ Q^5 := by
    have hh := mul_le_mul (mul_le_mul (hpair (candidateLow e) (S e.1.1 \ e.2.1))
      (hpair (candidateHigh e) (S e.1.2 \ e.2.2))
      (mul_nonneg (regularCoefficientWeight_nonneg _ _ _ _ _) (regularResidueWeight_nonneg _ _ _ _ _))
      (mul_nonneg hQ hQ)) ((hcap C).2 (candidateQuotient e))
      (regularCoefficientWeight_nonneg _ _ _ _ _) (by positivity)
    convert hh using 1; ring
  rw [candidateMeanWeight_eq]
  change W/(B : ℝ)*χ e*independentRootMean B L τ C ≤ _
  calc
    _ ≤ W/(B : ℝ)*independentRootMean B L τ C :=
      mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (div_nonneg hW hB0.le) (hχ e))
        (independentRootMean_nonneg _ _ _ _)
    _ ≤ (Q^5/(B : ℝ))*(B : ℝ)^ε :=
      mul_le_mul (div_le_div_of_nonneg_right hcapW hB0.le) ((hroot L τ C).trans hgrow)
        (independentRootMean_nonneg _ _ _ _) (by positivity)
    _ = (B : ℝ)^(5*(weightExponent τ+ε)+ε-1) := by
      have hp : (B : ℝ)^(5*(weightExponent τ+ε)+ε-1) =
          ((B : ℝ)^(weightExponent τ+ε))^5*(B : ℝ)^ε/(B : ℝ) := by
        calc
          _ = (B : ℝ)^((weightExponent τ+ε)*5+ε)/(B : ℝ) := by
            rw [Real.rpow_sub hB0,Real.rpow_one]
            congr 2
            ring
          _ = ((B : ℝ)^((weightExponent τ+ε)*5)*(B : ℝ)^ε)/(B : ℝ) := by
            rw [Real.rpow_add hB0]
          _ = _ := by
            rw [Real.rpow_mul hB0.le]
            norm_num
      rw [hp]
      dsimp [Q]
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hB.le) hexp

end JointDickman

end OAI
