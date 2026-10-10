import OAI.NumberTheory.JointDickman.Counting.CoarseCoefficientVariation

namespace OAI

/-! # Lipschitz dependence of the spatial model on its lag parameter -/
namespace JointDickman
open Finset Classical

theorem histogramLocation_le {m B : ℕ} (hB : 0 < B)
    {t L U : ℝ} {k : ℤ} {i : Fin (channelFineCount m B)}
    (hi : i ∈ geometricHistogramWindow m B t L U k) :
    Real.exp ((B : ℝ)*channelLower (channelFineCount m B) i)/Real.exp ((k : ℝ)*t) ≤ Real.exp U := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hh := (le_div_iff₀ hBr).mp (mem_filter.mp hi).2.1
  rw [← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem endpointSpatialWeight_parameter_difference {m B : ℕ} (hB : 0 < B)
    {t L U D M₁ M₂ β γ : ℝ} (hD : 0 ≤ D) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (d : ℤ → ℝ) (w₁ w₂ w : ℝ → ℝ) {K : NNReal} (hw : LipschitzWith K w)
    (k : ℤ) (hd : |d k| ≤ D) (hw₁ : ∀ z, |w₁ z| ≤ M₁) (hw₂ : ∀ z, |w₂ z| ≤ M₂)
    (i j : Fin (channelFineCount m B))
    (hi : i ∈ geometricHistogramWindow m B t L U k)
    (hj : j ∈ geometricHistogramWindow m B t L U k) :
    |endpointSpatialWeight m B t β d w₁ w₂ w k i j-
      endpointSpatialWeight m B t γ d w₁ w₂ w k i j| ≤
      D*M₁*M₂*(K : ℝ)*Real.exp U*|β-γ| := by
  let x := Real.exp ((B : ℝ)*channelLower (channelFineCount m B) i)/Real.exp ((k : ℝ)*t)
  let y := Real.exp ((B : ℝ)*channelLower (channelFineCount m B) j)/Real.exp ((k : ℝ)*t)
  have hx0 : 0 < x := div_pos (Real.exp_pos _) (Real.exp_pos _)
  have hy0 : 0 < y := div_pos (Real.exp_pos _) (Real.exp_pos _)
  have hx : x ≤ Real.exp U := histogramLocation_le hB hi
  have hy : y ≤ Real.exp U := histogramLocation_le hB hj
  have hxy : |x-y| ≤ Real.exp U := abs_le.mpr ⟨by linarith,by linarith⟩
  have hl := hw.dist_le_mul (β*x-β*y) (γ*x-γ*y)
  rw [Real.dist_eq,Real.dist_eq,show β*x-β*y-(γ*x-γ*y) = (β-γ)*(x-y) by ring,abs_mul] at hl
  have hl' : |w (β*x-β*y)-w (γ*x-γ*y)| ≤ (K : ℝ)*|β-γ| *Real.exp U :=
    by
      have hh := hl.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hxy (abs_nonneg _)) K.coe_nonneg)
      simpa only [mul_assoc] using hh
  have hc : |d k*w₁ x*w₂ y| ≤ D*M₁*M₂ := by
    rw [abs_mul,abs_mul]
    exact mul_le_mul (mul_le_mul hd (hw₁ x) (abs_nonneg _) hD) (hw₂ y) (abs_nonneg _) (mul_nonneg hD hM₁)
  change |d k*w₁ x*w₂ y*w (β*x-β*y)-d k*w₁ x*w₂ y*w (γ*x-γ*y)| ≤ _
  rw [← mul_sub,abs_mul]
  have hh := mul_le_mul hc hl' (abs_nonneg _) (by positivity : 0 ≤ D*M₁*M₂)
  convert hh using 1
  ring


theorem geometric_coarseCoefficient_parameter_difference {m B : ℕ}
    (hm : 0 < m) (hB : 1 ≤ B)
    {t L U D M₁ M₂ β γ : ℝ} (ht : 0 < t) (hLU : L ≤ U)
    (hD : 0 ≤ D) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (S : Finset ℤ) (d : ℤ → ℝ) (w₁ w₂ w : ℝ → ℝ)
    {K : NNReal} (hw : LipschitzWith K w)
    (hd : ∀ k ∈ S, |d k| ≤ D) (hw₁ : ∀ z, |w₁ z| ≤ M₁) (hw₂ : ∀ z, |w₂ z| ≤ M₂)
    (a b : Fin m) :
    |primeCoarseCoefficient m B
        (geometricWindowKernel m B t L U S (endpointSpatialWeight m B t β d w₁ w₂ w)) a b-
      primeCoarseCoefficient m B
        (geometricWindowKernel m B t L U S (endpointSpatialWeight m B t γ d w₁ w₂ w)) a b| ≤
      (channelMesh m*(2*(((1+U-L)/t+1)*(D*M₁*M₂*(K : ℝ)*Real.exp U))*(U-L+2)))*|β-γ| := by
  have hh := geometric_coarseCoefficient_difference hm hB ht hLU
    (show 0 ≤ D*M₁*M₂*(K : ℝ)*Real.exp U*|β-γ| by positivity) S
    (endpointSpatialWeight m B t β d w₁ w₂ w)
    (endpointSpatialWeight m B t γ d w₁ w₂ w)
    (fun k hk i j hi hj => endpointSpatialWeight_parameter_difference (by omega)
      hD hM₁ hM₂ d w₁ w₂ w hw k (hd k hk) hw₁ hw₂ i j hi hj) a b
  convert hh using 1
  ring

end JointDickman

end OAI
