import OAI.NumberTheory.JointDickman.Amplification.SingularSeries
import OAI.NumberTheory.JointDickman.Amplification.SingularFactor

namespace OAI

/-! # Elementary lag moments of the singular series -/

namespace JointDickman
open Finset

theorem totient_ratio_le_singularFactor {j : ℕ} (hj : 0 < j) :
    (j : ℝ)/j.totient ≤ singularFactor 24 j := by
  have hjr : (0 : ℝ) < j := by exact_mod_cast hj
  have hp (p : ℕ) (h : p ∈ j.primeFactors) : (2 : ℝ) ≤ p := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors h).two_le
  have hfactor (p : ℕ) (h : p ∈ j.primeFactors) : 0 < 1-1/(p : ℝ) := by
    have hpp := hp p h
    exact sub_pos.mpr ((div_lt_one (by linarith)).mpr (by linarith))
  have hprod : (0 : ℝ) < ∏ p ∈ j.primeFactors, (1-1/(p : ℝ)) := prod_pos hfactor
  have he : (j : ℝ)/j.totient = ∏ p ∈ j.primeFactors, (1-1/(p : ℝ))⁻¹ := by
    rw [totient_eq_prime_product_real,prod_inv_distrib]
    field_simp
  rw [he]
  apply prod_le_prod₀
  · intro p h
    exact inv_nonneg.mpr (hfactor p h).le
  · intro p h
    have hpp := hp p h
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hp1 : (0 : ℝ) < p-1 := by linarith
    have heq : (1-1/(p : ℝ))⁻¹ = p/(p-1) := by field_simp
    rw [heq]
    apply (div_le_iff₀ hp1).mpr
    have hh : (1+24/(p : ℝ))*(p-1)-(p : ℝ) = (23*p-24)/p := by field_simp; ring
    have hnonneg : 0 ≤ (23*(p : ℝ)-24)/p := div_nonneg (by linarith) (by linarith)
    linarith

theorem singularSeries_le_singularFactor
    (hMP : PublishedInputs.PrimeProductMertensInput) {j : ℕ} (hj : 0 < j) :
    singularSeries j ≤ singularFactor 24 j :=
  (singularSeries_bounds hMP j).2.trans (totient_ratio_le_singularFactor hj)

theorem singularSeries_moment (hMP : PublishedInputs.PrimeProductMertensInput)
    (r U : ℕ) :
    (∑ j ∈ Ioc 0 U, singularSeries j^r) ≤
      Real.exp ((r : ℝ)*24*(1+24)^(r-1))*U := by
  refine (sum_le_sum (fun j hj => ?_)).trans
    (singularFactor_nat_moment (by norm_num : (0 : ℝ) ≤ 24) r U)
  exact pow_le_pow_left₀ (singularSeries_bounds hMP j).1
    (singularSeries_le_singularFactor hMP (mem_Ioc.mp hj).1) r

end JointDickman

end OAI
