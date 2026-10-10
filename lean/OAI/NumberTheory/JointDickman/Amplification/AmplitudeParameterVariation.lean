import OAI.NumberTheory.JointDickman.Counting.CoarseCoefficientVariation

namespace OAI

/-! # Variation of coarse coefficients under changing box amplitudes -/
namespace JointDickman
open Finset Classical

theorem endpointSpatialWeight_amplitude_difference (m B : ℕ) (t β : ℝ)
    (d e : ℤ → ℝ) (w₁ w₂ w : ℝ → ℝ) {D M₁ M₂ M₀ : ℝ}
    (hD : 0 ≤ D) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (k : ℤ) (hd : |d k-e k| ≤ D) (hw₁ : ∀ z, |w₁ z| ≤ M₁)
    (hw₂ : ∀ z, |w₂ z| ≤ M₂) (hw : ∀ z, |w z| ≤ M₀)
    (i j : Fin (channelFineCount m B)) :
    |endpointSpatialWeight m B t β d w₁ w₂ w k i j-
      endpointSpatialWeight m B t β e w₁ w₂ w k i j| ≤ D*M₁*M₂*M₀ := by
  let x := Real.exp ((B : ℝ)*channelLower (channelFineCount m B) i)/Real.exp ((k : ℝ)*t)
  let y := Real.exp ((B : ℝ)*channelLower (channelFineCount m B) j)/Real.exp ((k : ℝ)*t)
  change |d k*w₁ x*w₂ y*w (β*x-β*y)-e k*w₁ x*w₂ y*w (β*x-β*y)| ≤ _
  rw [show d k*w₁ x*w₂ y*w (β*x-β*y)-e k*w₁ x*w₂ y*w (β*x-β*y) =
    (d k-e k)*w₁ x*w₂ y*w (β*x-β*y) by ring]
  simp only [abs_mul]
  exact mul_le_mul (mul_le_mul (mul_le_mul hd (hw₁ x) (abs_nonneg _) hD)
    (hw₂ y) (abs_nonneg _) (mul_nonneg hD hM₁)) (hw _) (abs_nonneg _)
    (mul_nonneg (mul_nonneg hD hM₁) hM₂)

theorem geometric_coarseCoefficient_amplitude_difference {m B : ℕ}
    (hm : 0 < m) (hB : 1 ≤ B) {t L U β D M₁ M₂ M₀ : ℝ}
    (ht : 0 < t) (hLU : L ≤ U) (hD : 0 ≤ D) (hM₁ : 0 ≤ M₁)
    (hM₂ : 0 ≤ M₂) (hM₀ : 0 ≤ M₀)
    (S : Finset ℤ) (d e : ℤ → ℝ) (w₁ w₂ w : ℝ → ℝ)
    (hd : ∀ k ∈ S, |d k-e k| ≤ D) (hw₁ : ∀ z, |w₁ z| ≤ M₁)
    (hw₂ : ∀ z, |w₂ z| ≤ M₂) (hw : ∀ z, |w z| ≤ M₀) (a b : Fin m) :
    |primeCoarseCoefficient m B
        (geometricWindowKernel m B t L U S (endpointSpatialWeight m B t β d w₁ w₂ w)) a b-
      primeCoarseCoefficient m B
        (geometricWindowKernel m B t L U S (endpointSpatialWeight m B t β e w₁ w₂ w)) a b| ≤
      channelMesh m*(2*(((1+U-L)/t+1)*(D*M₁*M₂*M₀))*(U-L+2)) := by
  exact geometric_coarseCoefficient_difference hm hB ht hLU (by positivity) S _ _
    (fun k hk i j _ _ => endpointSpatialWeight_amplitude_difference m B t β d e w₁ w₂ w
      hD hM₁ hM₂ k (hd k hk) hw₁ hw₂ hw i j) a b

end JointDickman

end OAI
