import OAI.Geometry.RCD.Metric.EuclideanSubquadraticRigidity
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! # Harmonic rigidity with only the dyadic bounds of the frame construction -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem euclidean_harmonic_affine_of_dyadic_growth {n : ℕ} (hn : 0 < n)
    {f : Euclidean n → ℝ} (hf : InnerProductSpace.HarmonicOnNhd f univ)
    {C q : ℝ} (hC : 0 < C) (hq : 0 < q) (hq4 : q < 4)
    (hb : ∀ k : ℕ, ∀ x ∈ ball 0 ((2 : ℝ)^k), |f x| ≤ C*q^k) :
    ∀ x, f x = f 0+fderiv ℝ f 0 x := by
  have hdecay : Tendsto (fun k : ℕ => C*q^k/((2 : ℝ)^k)^2) atTop (𝓝 0) := by
    have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (show 0 ≤ q/4 by positivity) (show q/4 < 1 by linarith)).const_mul C
    simp only [mul_zero] at hh
    convert hh using 1
    funext k
    have hpow : ((2 : ℝ)^k)^2 = (4 : ℝ)^k := by
      rw [← pow_mul,Nat.mul_comm,pow_mul]
      norm_num
    rw [hpow,div_pow]
    ring
  exact euclidean_harmonic_affine_of_subquadratic_bounds hn hf
    (fun k : ℕ => (2 : ℝ)^k) (fun k => C*q^k)
    (fun _ => by positivity) (fun _ => by positivity)
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num)) hdecay hb

end RegularPointCoordinates

end

end OAI
