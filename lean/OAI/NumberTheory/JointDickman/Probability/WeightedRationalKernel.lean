import OAI.NumberTheory.JointDickman.Probability.RationalKernelProgressions
import OAI.NumberTheory.JointDickman.Arithmetic.TotientWeightedKernel
import OAI.NumberTheory.JointDickman.Amplification.GcdReciprocalMean

namespace OAI

/-! # A quantitative totient-weighted rational geometric-kernel bound -/
namespace JointDickman
open Finset

private lemma rational_progression_weighted_bound (q : ℕ) (hq : 0 < q)
    (a : ℕ) (ha : a.Coprime q) (d : ℕ) (hd : 0 < d) (N X : ℕ) :
    (1/(d:ℝ)) * (∑ k ∈ Ioc 0 (X/d), geometricSquareKernel N ((a:ℝ)/q*d*k)) ≤
      ((N:ℝ)^2*X/q)*((Nat.gcd d q:ℝ)/(d:ℝ)^2) +
      ((N:ℝ)*X)*(1/(d:ℝ)^2) + (2*(N:ℝ)*q)*(1/(d:ℝ)) := by
  have hi : Ioc 0 (X/d) = Icc 1 (X/d) := by
    ext k
    simp only [mem_Ioc,mem_Icc]
    omega
  have hp := rational_geometric_progression_bound q hq a ha d N (X/d)
  rw [←hi] at hp
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  have hfloor : ((X/d:ℕ):ℝ) ≤ (X:ℝ)/d := by
    apply (le_div_iff₀ hdR).mpr
    exact_mod_cast Nat.div_mul_le_self X d
  have hquot : ((q/Nat.gcd d q:ℕ):ℝ) ≤ q := by exact_mod_cast Nat.div_le_self q (Nat.gcd d q)
  have hpeak : (N:ℝ)^2*((X/d:ℕ):ℝ)*(Nat.gcd d q:ℝ)/q ≤
      (N:ℝ)^2*((X:ℝ)/d)*(Nat.gcd d q:ℝ)/q := by
    convert mul_le_mul_of_nonneg_left hfloor
      (show 0 ≤ (N:ℝ)^2*(Nat.gcd d q:ℝ)/q by positivity) using 1 <;> ring
  have hrest : (N:ℝ)*(((X/d:ℕ):ℝ)+2*((q/Nat.gcd d q:ℕ):ℝ)) ≤
      (N:ℝ)*((X:ℝ)/d+2*q) := by
    gcongr
  have hm := mul_le_mul_of_nonneg_left (hp.trans (add_le_add hpeak hrest))
    (show 0 ≤ 1/(d:ℝ) by positivity)
  convert hm using 1
  field_simp
  ring

/-- This bound allows an extra logarithm in the rational denominator, which
is harmless for the polylogarithmic minor arcs used in this application. -/
theorem totient_weighted_rational_kernel_bound (q : ℕ) (hq : 0 < q)
    (a : ℕ) (ha : a.Coprime q) (N X : ℕ) :
    (∑ h ∈ Ioc 0 X, ((h:ℝ)/h.totient)*geometricSquareKernel N ((a:ℝ)/q*h)) ≤
      2*Real.exp 2 * ((N:ℝ)^2*X*(1+Real.log q)/q +
        (N:ℝ)*X + (N:ℝ)*q*(1+Real.log X)) := by
  have hstart := totient_weighted_sum_le_divisor_sum
    (fun h => geometricSquareKernel N ((a:ℝ)/q*h))
    (fun h => geometricSquareKernel_nonneg _ _) X
  have hp (d : ℕ) (hd : d ∈ Ioc 0 X) :
      (1/(d:ℝ)) * (∑ k ∈ Ioc 0 (X/d), geometricSquareKernel N ((a:ℝ)/q*(d*k:ℕ))) ≤
      ((N:ℝ)^2*X/q)*((Nat.gcd d q:ℝ)/(d:ℝ)^2) +
      ((N:ℝ)*X)*(1/(d:ℝ)^2) + (2*(N:ℝ)*q)*(1/(d:ℝ)) := by
    simpa only [Nat.cast_mul,mul_assoc] using
      rational_progression_weighted_bound q hq a ha d (mem_Ioc.mp hd).1 N X
  have hsum := sum_le_sum hp
  simp only [sum_add_distrib,←mul_sum] at hsum
  have hbound : ((N:ℝ)^2*X/q)*(∑ d ∈ Ioc 0 X, (Nat.gcd d q:ℝ)/(d:ℝ)^2) +
      ((N:ℝ)*X)*(∑ d ∈ Ioc 0 X, 1/(d:ℝ)^2) +
      (2*(N:ℝ)*q)*(∑ d ∈ Ioc 0 X, 1/(d:ℝ)) ≤
      ((N:ℝ)^2*X/q)*(2*(1+Real.log q)) + ((N:ℝ)*X)*2 +
        (2*(N:ℝ)*q)*(1+Real.log X) := by
    exact add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left (gcd_reciprocal_square_sum q X hq) (by positivity))
      (mul_le_mul_of_nonneg_left (reciprocal_square_initial_sum X) (by positivity)))
      (mul_le_mul_of_nonneg_left (reciprocal_initial_sum X) (by positivity))
  have hh := hstart.trans (mul_le_mul_of_nonneg_left (hsum.trans hbound) (Real.exp_pos 2).le)
  convert hh using 1
  ring

end JointDickman

end OAI
