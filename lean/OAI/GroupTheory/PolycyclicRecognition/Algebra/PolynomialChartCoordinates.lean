import OAI.GroupTheory.PolycyclicRecognition.Algebra.PositiveRescaling
import OAI.GroupTheory.PolycyclicRecognition.Geometry.FiniteLieNorm

namespace OAI

/-! # Polynomial logarithm bounds for the actual scaled coordinate charts -/

noncomputable section

namespace PolycyclicRecognition

open Module
open scoped BigOperators

/-- Unit letter weights give the ordinary bracket length. -/
theorem bracketWordExponent_one {I : Type*} [Fintype I] [DecidableEq I]
    (w : FreeMagma I) : bracketWordExponent (fun _ => 1) w = bracketWordLength w := by
  induction w using FreeMagma.rec with
  | of i => simp [bracketWordLength]
  | mul u v hu hv =>
      change bracketWordExponent (fun _ => 1) (u * v) = _
      rw [bracketWordExponent_mul, hu, hv]
      simp only [bracketWordLength, Nat.cast_add]

/-- Integer coordinate weights make the logarithm of every bounded chart
point polynomially bounded in the actual scale, in any fixed reference
basis. This estimate does not assume a limiting group or metric. -/
theorem norm_polynomial_chart_log_le
    {L J K : Type*} [LieRing L] [LieAlgebra ℝ L] [Fintype J] [Fintype K]
    (b : Basis J ℝ L) (b₀ : Basis K ℝ L) (cost : J → ℕ)
    (p : ℕ) (hp : ∀ j, cost j ≤ p)
    {r : ℝ} (hr : 1 ≤ r) (z : J → ℝ) :
    ‖b₀.equivFun ((exponentialRescaleBasis b (fun j => (cost j : ℝ)) (Real.log r)).equivFun.symm z)‖ ≤
      (∑ j, ‖b₀.equivFun (b j)‖) * ‖z‖ * (1 + r) ^ p := by
  have hr0 : 0 < r := by linarith
  rw [Basis.equivFun_symm_apply, map_sum]
  apply (norm_sum_le _ _).trans
  have hterm (j : J) :
      ‖b₀.equivFun (z j • exponentialRescaleBasis b (fun j => (cost j : ℝ)) (Real.log r) j)‖ ≤
        ‖b₀.equivFun (b j)‖ * ‖z‖ * (1 + r) ^ p := by
    simp only [exponentialRescaleBasis, Basis.unitsSMul_apply, Units.smul_def,
      Units.val_mk0, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hexp : Real.exp (Real.log r * (cost j : ℝ)) = r ^ cost j := by
      rw [mul_comm, Real.exp_nat_mul, Real.exp_log hr0]
    rw [hexp]
    have hpow : r ^ cost j ≤ (1 + r) ^ p :=
      (pow_le_pow_left₀ hr0.le (by linarith) _).trans
        (pow_le_pow_right₀ (by linarith) (hp j))
    have hz := norm_le_pi_norm z j
    rw [Real.norm_eq_abs] at hz
    nlinarith [mul_le_mul hz hpow (pow_nonneg hr0.le _) (norm_nonneg z),
      norm_nonneg (b₀.equivFun (b j))]
  calc
    _ ≤ ∑ j, ‖b₀.equivFun (b j)‖ * ‖z‖ * (1 + r) ^ p :=
      Finset.sum_le_sum (fun j _ => hterm j)
    _ = _ := by rw [Finset.sum_mul, Finset.sum_mul]

end PolycyclicRecognition

end

end OAI
