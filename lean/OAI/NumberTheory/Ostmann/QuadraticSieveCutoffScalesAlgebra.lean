import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

namespace Ostmann.QuadraticSieve

lemma cutoff_scale_power_identity {M N ξ : ℝ} (hM : 0<M) (hN : 0<N) :
    Real.sqrt M * (N^2/M)^(ξ-1/2) = M^(1-ξ)*N^(2*ξ-1) := by
  rw [Real.div_rpow (sq_nonneg N) hM.le, Real.sqrt_eq_rpow]
  have he : (N^2)^(ξ-1/2) = N^(2*ξ-1) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hN.le]
    congr 1
    ring
  rw [he]
  calc
    M^(1/2:ℝ)*(N^(2*ξ-1)/M^(ξ-1/2)) =
        (M^(1/2:ℝ)/M^(ξ-1/2))*N^(2*ξ-1) := by ring
    _ = _ := by
      rw [← Real.rpow_sub hM]
      congr 2
      ring

theorem cutoff_scale_scalar_bound {M N T K ξ : ℝ}
    (hM : 1≤M) (hN : 0<N) (hT : 1≤T) (hK0 : 0≤K)
    (hK : K≤2*N^2/M*T+1) (hξ1 : 1<ξ) (hξ2 : ξ≤2) :
    Real.sqrt M*K^(ξ-1/2) ≤
      16*T^2*(M+M^(1-ξ)*N^(2*ξ-1)) := by
  have hMp : 0<M := by linarith
  have hr : 0≤ξ-1/2 := by linarith
  have hT0 : 0<T := by linarith
  have hsqrt : Real.sqrt M ≤ M := Real.sqrt_le_self_iff.mpr (Or.inr hM)
  have htwo : (2:ℝ)^(ξ-1/2) ≤ 4 := by
    calc
      _ ≤ (2:ℝ)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = _ := by norm_num
  have hTp : T^(ξ-1/2) ≤ T^2 := by
    simpa only [Real.rpow_two] using
      Real.rpow_le_rpow_of_exponent_le hT (show ξ-1/2≤2 by linarith)
  have hT2 : 1≤T^2 := by nlinarith
  have hnonneg : 0≤M^(1-ξ)*N^(2*ξ-1) := by positivity
  let A : ℝ := 2*N^2/M*T
  have hA : 0<A := by dsimp [A]; positivity
  by_cases hA1 : A≤1
  · have hK2 : K≤2 := by dsimp only [A] at hA1; linarith
    have hKr : K^(ξ-1/2)≤4 :=
      (Real.rpow_le_rpow hK0 hK2 hr).trans htwo
    calc
      _ ≤ Real.sqrt M*4 := mul_le_mul_of_nonneg_left hKr (Real.sqrt_nonneg _)
      _ ≤ 4*M := by nlinarith
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hT2 (show 0≤M by linarith),
        mul_nonneg (sq_nonneg T) hnonneg]
  · have hK2A : K≤2*A := by dsimp only [A] at *; linarith
    have hpow : K^(ξ-1/2) ≤ 4*A^(ξ-1/2) := by
      calc
        _ ≤ (2*A)^(ξ-1/2) := Real.rpow_le_rpow hK0 hK2A hr
        _ = (2:ℝ)^(ξ-1/2)*A^(ξ-1/2) := Real.mul_rpow (by norm_num) hA.le
        _ ≤ _ := mul_le_mul_of_nonneg_right htwo (by positivity)
    have hAr : A^(ξ-1/2) ≤ 4*(N^2/M)^(ξ-1/2)*T^2 := by
      have he : A = 2*(N^2/M)*T := by dsimp only [A]; ring
      rw [he, Real.mul_rpow (by positivity) hT0.le,
        Real.mul_rpow (by norm_num : (0:ℝ)≤2) (by positivity)]
      exact mul_le_mul (mul_le_mul_of_nonneg_right htwo (by positivity)) hTp
        (by positivity) (by positivity)
    calc
      _ ≤ Real.sqrt M*(4*A^(ξ-1/2)) :=
        mul_le_mul_of_nonneg_left hpow (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt M*(4*(4*(N^2/M)^(ξ-1/2)*T^2)) := by
        gcongr
      _ = 16*T^2*(M^(1-ξ)*N^(2*ξ-1)) := by
        rw [← cutoff_scale_power_identity hMp hN]
        ring
      _ ≤ _ := by gcongr; linarith

end Ostmann.QuadraticSieve

end OAI
