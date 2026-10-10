import Mathlib
import OAI.RepresentationTheory.PartialPermutation.DiagramCounts

namespace OAI

section
namespace PartialPermutation
namespace DiagramCounting
noncomputable section
open Finset
open Filter in

lemma partitionCount_subexponential (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, (partitionCount n : ℝ) ≤ Real.exp (δ*n) := by
  have hl := (isLittleO_log_rpow_atTop (show (0:ℝ)<1/2 by norm_num)).bound
    (show 0 < δ/4 by positivity)
  have ht : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun n => le_add_of_nonneg_right (show (0:ℝ)≤1 by norm_num))
      tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually hl, eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hn1' : (1:ℝ) ≤ n := by exact_mod_cast hn1
  have hs : 0 ≤ Real.sqrt (n+1) := Real.sqrt_nonneg _
  have hsq := Real.sq_sqrt (show (0:ℝ)≤n+1 by positivity)
  have hl0 : 0 ≤ Real.log ((n:ℝ)+1) := Real.log_nonneg (by linarith)
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hl0,
    ← Real.sqrt_eq_rpow,abs_of_nonneg hs] at hn
  have hnrt : (n.sqrt:ℝ) ≤ Real.sqrt (n+1) := by
    have h := Nat.sqrt_le n
    have hr : (n.sqrt:ℝ)^2 ≤ n := by simpa only [pow_two] using (show (n.sqrt:ℝ)*(n.sqrt:ℝ)≤n by exact_mod_cast h)
    nlinarith [show (0:ℝ)≤n.sqrt by positivity]
  have hexp : (2*(n.sqrt:ℝ))*Real.log ((n:ℝ)+1) ≤ δ*n := by
    calc
      _ ≤ (2*Real.sqrt (n+1))*((δ/4)*Real.sqrt (n+1)) :=
        mul_le_mul (by linarith) hn hl0 (by positivity)
      _ = δ/2*((n:ℝ)+1) := by nlinarith
      _ ≤ δ*n := by nlinarith
  calc
    (partitionCount n : ℝ) ≤ ((n+1)^(2*n.sqrt):ℕ) := by
      exact_mod_cast partitionCount_le_sqrt n
    _ = Real.exp ((2*(n.sqrt:ℝ))*Real.log ((n:ℝ)+1)) := by
      push_cast
      rw [show (2:ℝ)*(n.sqrt:ℝ)=((2*n.sqrt:ℕ):ℝ) by push_cast; rfl,
        Real.exp_nat_mul, Real.exp_log (by positivity)]
    _ ≤ Real.exp (δ*n) := Real.exp_le_exp.mpr hexp

end
end DiagramCounting
end PartialPermutation

end

end OAI
