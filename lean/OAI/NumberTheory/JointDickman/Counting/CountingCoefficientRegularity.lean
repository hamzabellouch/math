import OAI.NumberTheory.JointDickman.Amplification.PolynomialTermAmplitudeVariation
import OAI.NumberTheory.JointDickman.Counting.CountingArithmeticFeatures

namespace OAI

/-! # Finite coefficients of the actual counting model and their regularity -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

noncomputable def countingTermCoefficient (P : MvPolynomial (Fin 4) ℝ)
    (d : Fin 4 →₀ ℕ) (m B j : ℕ) (c : ℕ → ℝ) (H : ℕ)
    (T σ : ℝ) (a b : Fin m) : ℝ :=
  weightedTermCoefficient P d m B j c H T (Real.log 2)
    (dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T))
    (fun _ => σ) (fun k => amplificationBump (Real.log (Real.exp ((k : ℝ)*Real.log 2)/T)/B)) a b

theorem countingPrimeKernel_coefficients (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) (B j : ℕ) (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
    (H : (Fin 4 →₀ ℕ) → ℕ) (T σ : ℝ) (x y : auxiliaryPrimes B → Bool) :
    countingPrimeKernel P m B j c H T σ x y =
      ∑ d ∈ P.support, ∑ a, ∑ b, countingTermCoefficient P d (m d) B j (c d) (H d) T σ a b*
        primeCoarseFeature (m d) B a x*primeCoarseFeature (m d) B b y := by
  unfold countingPrimeKernel weightedPolynomialPrimeKernel
  apply sum_congr rfl
  intro d _
  rw [weightedPolynomialTermKernel_coefficients]
  rfl

theorem countingTermCoefficient_regular
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (P : MvPolynomial (Fin 4) ℝ) (d : Fin 4 →₀ ℕ)
    {m : ℕ} (hm : 0 < m) (c : ℕ → ℝ) (hc : c 0 = squarefreeLeadingConstant (1/2))
    (H : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ B : ℕ in atTop, ∀ (j k : ℕ) (T σ σ' : ℝ),
      1 ≤ T → Real.log T ≤ (B : ℝ)/10 → η*T ≤ j → η*T ≤ k →
      |σ| ≤ 3 → |σ'| ≤ 3 → ∀ a b : Fin m,
      |countingTermCoefficient P d m B j c H T σ a b-
        countingTermCoefficient P d m B k c H T σ' a b| ≤ C*(|(j : ℝ)-k|/T+|σ-σ'|) := by
  obtain ⟨C₁,hC₁,hLag⟩ := weightedTermCoefficient_lag_variation hM hMP P d hm c hc H
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)) hη
  obtain ⟨C₂,hC₂,hAmp⟩ := weightedTermCoefficient_parameter_variation hM hMP P d hm c hc H
    (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  refine ⟨C₁+C₂,add_nonneg hC₁ hC₂,?_⟩
  filter_upwards [hLag,hAmp,eventually_ge_atTop 30] with B hLag hAmp hB
  intro j k T σ σ' hT hlog hj hk hσ hσ' a b
  let S := dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T)
  let r := fun u : ℤ => amplificationBump (Real.log (Real.exp ((u : ℝ)*Real.log 2)/T)/B)
  have hS : ∀ u ∈ S, (9/10 : ℝ)*B ≤ Real.log (Real.exp ((u : ℝ)*Real.log 2)/T) := by
    intro u hu
    exact (((dyadic_scale_window hB hT hlog).2.1 u hu).2).1
  have hr : ∀ u ∈ S, |r u| ≤ 1 := by
    intro u _
    rw [abs_of_nonneg (amplificationBump_bounds _).1]
    exact (amplificationBump_bounds _).2
  have hl := hLag j k T (lt_of_lt_of_le zero_lt_one hT) hj hk S hS (fun _ => σ)
    (fun _ _ => hσ) r hr a b
  have ha := hAmp k T S hS (fun _ => σ) (fun _ => σ') (fun _ _ => hσ) (fun _ _ => hσ')
    r hr |σ-σ'| (abs_nonneg _) (fun _ _ => le_rfl) a b
  change |countingTermCoefficient P d m B j c H T σ a b-
    countingTermCoefficient P d m B k c H T σ a b| ≤ _ at hl
  change |countingTermCoefficient P d m B k c H T σ a b-
    countingTermCoefficient P d m B k c H T σ' a b| ≤ _ at ha
  have ht := (abs_sub_le (countingTermCoefficient P d m B j c H T σ a b)
    (countingTermCoefficient P d m B k c H T σ a b)
    (countingTermCoefficient P d m B k c H T σ' a b)).trans (add_le_add hl ha)
  apply ht.trans
  rw [mul_div_assoc]
  have hnn : 0 ≤ |(j : ℝ)-k|/T := div_nonneg (abs_nonneg _) (by linarith)
  nlinarith [mul_nonneg hC₁ (abs_nonneg (σ-σ')),mul_nonneg hC₂ hnn]

end JointDickman

end OAI
