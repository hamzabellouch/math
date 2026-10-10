import OAI.NumberTheory.TotientAsymptotic.RoughIntervalMoment

namespace OAI

/-! The interval allocation bound with arbitrary prime multiplicities. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma rough_collision_mass {c U V I H : ℝ} (hc : 1 ≤ c) (hcU : 2*c ≤ U)
    (hU : 2 ≤ U) (hUV : U ≤ V) (Q : Finset ℕ)
    (hQ : ∀ n ∈ Q,0 < n ∧ (n.primeFactorsList.length:ℝ) ≤ I ∧
      ∀ p ∈ n.primeFactorsList,U < (p:ℝ) ∧ (p:ℝ) ≤ V)
    (hH : (∑ p ∈ (primesUpTo V).filter (fun p : ℕ => U < (p:ℝ)),(p:ℝ)⁻¹) ≤ H)
    (hquad : 2*c^2*(∑ p ∈ (primesUpTo V).filter (fun p : ℕ => U < (p:ℝ)),((p:ℝ)^2)⁻¹) ≤ 1)
    (hIH : c*H ≤ I) :
    (∑ n ∈ Q,c^(2*n.primeFactorsList.length)/(n:ℝ)) ≤
      Real.exp (I*(Real.log c+1)+1) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hm := rough_interval_reciprocal_moment hc0.le hcU hU hUV Q
    (fun n hn => ⟨(hQ n hn).1,(hQ n hn).2.2⟩)
  have ht : (∑ n ∈ Q,c^(2*n.primeFactorsList.length)/(n:ℝ)) ≤
      c^I*(∑ n ∈ Q,c^n.primeFactorsList.length/(n:ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    have hh := Real.rpow_le_rpow_of_exponent_le hc (hQ n hn).2.1
    rw [Real.rpow_natCast] at hh
    have hh' := mul_le_mul_of_nonneg_right hh
      (show 0 ≤ c^n.primeFactorsList.length/(n:ℝ) by positivity)
    convert hh' using 1
    rw [two_mul,pow_add]
    ring
  calc
    _ ≤ c^I*(∑ n ∈ Q,c^n.primeFactorsList.length/(n:ℝ)) := ht
    _ ≤ c^I*Real.exp (c*(∑ p ∈ (primesUpTo V).filter (fun p : ℕ => U < (p:ℝ)),(p:ℝ)⁻¹)+
        2*c^2*(∑ p ∈ (primesUpTo V).filter (fun p : ℕ => U < (p:ℝ)),((p:ℝ)^2)⁻¹)) :=
      mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg hc0.le I)
    _ ≤ c^I*Real.exp (I+1) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hc0.le I)
      apply Real.exp_le_exp.mpr
      linarith [mul_le_mul_of_nonneg_left hH hc0.le]
    _ = _ := by
      rw [Real.rpow_def_of_pos hc0,← Real.exp_add]
      congr 1
      ring

end TotientAsymptotic

end

end OAI
