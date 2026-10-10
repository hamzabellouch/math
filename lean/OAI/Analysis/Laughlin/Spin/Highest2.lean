import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

noncomputable def ladder (A p : ℕ) : ℝ :=
  Real.sqrt (((p : ℝ)+1)*(A-p : ℕ))

noncomputable def highestRaw (A B z p : ℕ) : ℝ :=
  if p ≤ z then (-1 : ℝ)^p * (z.choose p : ℝ) /
    Real.sqrt ((A.choose p : ℝ)*(B.choose (z-p) : ℝ)) else 0

theorem ladder_pos (A p : ℕ) (hp : p < A) : 0 < ladder A p := by
  unfold ladder
  apply Real.sqrt_pos.mpr
  have h : (0 : ℝ) < (A-p : ℕ) := by exact_mod_cast (show 0 < A-p by omega)
  positivity

theorem choose_step_real (A p : ℕ) (hp : p ≤ A) :
    ((p : ℝ)+1)*(A.choose (p+1) : ℝ) =
      (A-p : ℕ)*(A.choose p : ℝ) := by
  have h := Nat.choose_succ_right_eq A p
  simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_sub hp,mul_comm] using
    congrArg (fun n : ℕ => (n : ℝ)) h

theorem sqrt_choose_step (A p : ℕ) (hp : p < A) :
    ladder A p * Real.sqrt (A.choose (p+1) : ℝ) =
      (A-p : ℕ)*Real.sqrt (A.choose p : ℝ) := by
  have hc := choose_step_real A p (by omega)
  have he : (ladder A p * Real.sqrt (A.choose (p+1) : ℝ))^2 =
      ((A-p : ℕ)*Real.sqrt (A.choose p : ℝ))^2 := by
    unfold ladder
    rw [mul_pow,mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity)]
    nlinarith [hc]
  have h₁ : 0 ≤ ladder A p * Real.sqrt (A.choose (p+1) : ℝ) := by
    exact mul_nonneg (le_of_lt (ladder_pos A p hp)) (Real.sqrt_nonneg _)
  have h₂ : 0 ≤ (A-p : ℕ)*Real.sqrt (A.choose p : ℝ) := by positivity
  nlinarith

theorem ladder_div_sqrt_choose (A p : ℕ) (hp : p < A) :
    ladder A p / Real.sqrt (A.choose (p+1) : ℝ) =
      ((p : ℝ)+1) / Real.sqrt (A.choose p : ℝ) := by
  have h₀ : 0 < (A.choose p : ℝ) := by exact_mod_cast Nat.choose_pos (by omega : p ≤ A)
  have h₁ : 0 < (A.choose (p+1) : ℝ) := by exact_mod_cast Nat.choose_pos (by omega : p+1 ≤ A)
  apply (div_eq_div_iff (ne_of_gt (Real.sqrt_pos.mpr h₁))
    (ne_of_gt (Real.sqrt_pos.mpr h₀))).mpr
  have hc := choose_step_real A p (by omega)
  have he : (ladder A p * Real.sqrt (A.choose p : ℝ))^2 =
      (((p : ℝ)+1)*Real.sqrt (A.choose (p+1) : ℝ))^2 := by
    unfold ladder
    rw [mul_pow,mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity)]
    nlinarith [hc]
  have hn₀ : 0 ≤ ladder A p * Real.sqrt (A.choose p : ℝ) :=
    mul_nonneg (le_of_lt (ladder_pos A p hp)) (Real.sqrt_nonneg _)
  have hn₁ : 0 ≤ ((p : ℝ)+1)*Real.sqrt (A.choose (p+1) : ℝ) := by positivity
  nlinarith

theorem highestRaw_raising (A B z p : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (hp : p < z) :
    ladder A p * highestRaw A B z (p+1) +
      ladder B (z-p-1) * highestRaw A B z p = 0 := by
  have hpA : p < A := by omega
  have hkB : z-p-1 < B := by omega
  have hk : z-(p+1) = z-p-1 := by omega
  have hk' : z-p = (z-p-1)+1 := by omega
  have hca : (Real.sqrt (A.choose p : ℝ)) ≠ 0 := by
    apply ne_of_gt; apply Real.sqrt_pos.mpr; exact_mod_cast Nat.choose_pos (by omega : p ≤ A)
  have hcb : (Real.sqrt (B.choose (z-p-1) : ℝ)) ≠ 0 := by
    apply ne_of_gt; apply Real.sqrt_pos.mpr; exact_mod_cast Nat.choose_pos (by omega : z-p-1 ≤ B)
  simp only [highestRaw,ite_eq_left (show p+1 ≤ z by omega),ite_eq_left (show p ≤ z by omega),hk]
  rw [Real.sqrt_mul (by positivity),Real.sqrt_mul (by positivity)]
  have hleft := ladder_div_sqrt_choose A p hpA
  have hright := ladder_div_sqrt_choose B (z-p-1) hkB
  rw [← hk'] at hright
  have hz := choose_step_real z p (by omega)
  have castk : ((z-p-1 : ℕ) : ℝ)+1 = (z-p : ℕ) := by exact_mod_cast hk'.symm
  rw [castk] at hright
  calc
    _ = (-1 : ℝ)^(p+1)*(z.choose (p+1) : ℝ) /
          Real.sqrt (B.choose (z-p-1) : ℝ) *
          (ladder A p / Real.sqrt (A.choose (p+1) : ℝ)) +
        (-1 : ℝ)^p*(z.choose p : ℝ) / Real.sqrt (A.choose p : ℝ) *
          (ladder B (z-p-1) / Real.sqrt (B.choose (z-p) : ℝ)) := by ring
    _ = _ := by rw [hleft,hright]
    _ = 0 := by rw [pow_succ]; field_simp; linear_combination -((-1 : ℝ)^p)*hz

end Laughlin.Spin

end OAI
