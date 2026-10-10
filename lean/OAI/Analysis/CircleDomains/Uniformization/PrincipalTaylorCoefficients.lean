import OAI.Analysis.CircleDomains.Reflection.HolomorphicCircleCoefficients
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Data.Nat.Choose.Cast

namespace OAI

/-! The principal Laurent coefficients are the Taylor coefficients of
its inverted remainder. The inverted derivative retains their exact weights. -/
open Set Filter Function Metric Real MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma diskTaylorCoefficient_mul_pow {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (n k : ℕ) : diskTaylorCoefficient (fun z => z^k*f z) (n+k) =
      diskTaylorCoefficient f n := by
  have hp : ContDiffAt ℂ (n+k) (fun z : ℂ => z^k) 0 :=
    (contDiff_id.pow k).contDiffAt
  have hd : ContDiffAt ℂ (n+k) f 0 := hf.contDiffAt
  unfold diskTaylorCoefficient
  rw [iteratedDeriv_fun_mul hp hd]
  simp only [iteratedDeriv_fun_pow_zero]
  rw [Finset.sum_eq_single k]
  · simp only [ite_true, Nat.add_sub_cancel_right]
    rw [Nat.cast_choose ℂ (by omega : k ≤ n+k), Nat.add_sub_cancel_right]
    have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    have hk : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    have hnk : ((n+k).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
  · intro i _ hik
    simp [hik]
  · intro hk
    exact (hk (Finset.mem_range.mpr (by omega))).elim

lemma diskTaylorCoefficient_deriv {f : ℂ → ℂ} (n : ℕ) :
    diskTaylorCoefficient (deriv f) n = (n+1 : ℂ)*diskTaylorCoefficient f (n+1) := by
  unfold diskTaylorCoefficient
  rw [← iteratedDeriv_succ', Nat.factorial_succ]
  push_cast
  have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hs : (n : ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  field_simp

lemma invertedPrincipalDerivative_coefficient {F : ℂ → ℂ}
    (hF : AnalyticAt ℂ (invertedPrincipalRemainder F) 0) (n : ℕ) :
    diskTaylorCoefficient (invertedPrincipalDerivative F) (n+2) =
      -(n+1 : ℂ) * diskTaylorCoefficient (invertedPrincipalRemainder F) (n+1) := by
  have he : diskTaylorCoefficient (invertedPrincipalDerivative F) (n+2) =
      -diskTaylorCoefficient (fun z => z^2*deriv (invertedPrincipalRemainder F) z) (n+2) := by
    unfold diskTaylorCoefficient invertedPrincipalDerivative
    rw [iteratedDeriv_const_sub (by omega) 1, iteratedDeriv_neg]
    ring
  rw [he, diskTaylorCoefficient_mul_pow hF.deriv n 2, diskTaylorCoefficient_deriv]
  ring

lemma principal_laurent_hasSum {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ (invertedPrincipalRemainder F) (ball 0 1))
    {z : ℂ} (hz : 1 < ‖z‖) :
    HasSum (fun n => diskTaylorCoefficient (invertedPrincipalRemainder F) (n+1) *
      (z⁻¹)^(n+1)) (F z-z) := by
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by linarith [norm_nonneg z])
  have hw : z⁻¹ ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball, dist_zero_right, norm_inv]
    exact (inv_lt_one₀ (by linarith : 0 < ‖z‖)).mpr hz
  have hs := Complex.hasSum_taylorSeries_on_ball hF.differentiableOn hw
  have hsum : HasSum (fun n => diskTaylorCoefficient (invertedPrincipalRemainder F) n *
      (z⁻¹)^n) (invertedPrincipalRemainder F z⁻¹) := by
    convert hs using 1
    funext n
    simp only [diskTaylorCoefficient, sub_zero, smul_eq_mul]
    ring
  have he := (hasSum_nat_add_iff' 1).mpr hsum
  simpa [diskTaylorCoefficient, invertedPrincipalRemainder, hz0] using he

end CircleDomainRigidity

end

end OAI
