import Mathlib
import OAI.Probability.LogConcave.JetEstimates.ForestTensor

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set
open scoped NNReal

lemma normalizedTensorMajorant_scale {n : ℕ} {a R : ℝ} (hR : 0<R) (ha : R^2≤a) :
    normalizedTensorMajorant n a≤normalizedTensorMajorant n 1/R^(n-2) := by
  let C : ℝ := ((n+1:ℕ):ℝ)^(2*(n+1))*(2*Real.pi^2)^n*((n.factorial:ℝ)^2)^2
  have hC : 0≤C := by dsimp [C]; positivity
  have hden : 0<(R^2)^(n-2) := pow_pos (sq_pos_of_pos hR) _
  have he : (R^2)^(n-2)=(R^(n-2))^2 := by rw [←pow_mul,←pow_mul]; congr 1; omega
  calc
    _ ≤ Real.sqrt (C/(R^2)^(n-2)) := by
      apply Real.sqrt_le_sqrt
      exact div_le_div_of_nonneg_left hC hden (pow_le_pow_left₀ (sq_nonneg R) ha _)
    _ = _ := by
      rw [Real.sqrt_div hC,he,Real.sqrt_sq (pow_nonneg hR.le _)]
      simp [normalizedTensorMajorant,C]

lemma conditionalMean_iterated_uniform_split {d n : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ R : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (hR : 0<R) (ha : R^2≤1-ρ^2) (y : Point d) :
    TensorEnergy.AllSplitBound
      (TensorEnergy.multilinearTensor (iteratedFDeriv ℝ n (conditionalFieldMean F x r ρ) y))
      (((lam:ℝ)*r)*normalizedTensorMajorant (n+1) 1/R^(n-1)) := by
  have hb := conditionalMean_iterated_allSplit hF x hr hlam hl hρ0 hρ1 y (n:=n)
  apply hb.mono (mul_nonneg (by positivity) (normalizedTensorMajorant_nonneg _ _))
  have hm := mul_le_mul_of_nonneg_left (normalizedTensorMajorant_scale (n:=n+1) hR ha)
    (show 0≤(lam:ℝ)*r by positivity)
  have he : n+1-2=n-1 := by omega
  simpa only [he,mul_div_assoc] using hm
end LogConcaveSampling

end

end

end

end OAI
