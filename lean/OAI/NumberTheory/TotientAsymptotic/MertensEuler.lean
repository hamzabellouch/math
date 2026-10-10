import OAI.NumberTheory.TotientAsymptotic.SmoothCofactorMoment
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SumIntegralComparisons

namespace OAI

/-! A finite Euler product controlled by a convergent real power series. -/
noncomputable section
open scoped BigOperators
open MeasureTheory Set
namespace TotientAsymptotic

private def negativePower (s : ℝ) : ℕ →* ℝ where
  toFun n := (n : ℝ)^(-s)
  map_one' := by simp
  map_mul' m n := by
    simp only [Nat.cast_mul,Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]

lemma negative_power_sum_le {s : ℝ} (hs : 1<s) :
    (∑' n : ℕ, (n : ℝ)^(-s)) ≤ 1+1/(s-1) := by
  have hsum : Summable (fun n : ℕ => (n : ℝ)^(-s)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have htail := AntitoneOn.tsum_comp_add_le_integral (f := fun x : ℝ => x^(-s)) 1
    (fun x hx y _ hxy => Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le (by simpa using hx)) hxy (by linarith))
    (integrableOn_Ioi_rpow_of_lt (by linarith : -s < -1) (by norm_num))
    (fun x hx => Real.rpow_nonneg (zero_lt_one.trans (by simpa using hx)).le _)
  simp only [Nat.cast_one] at htail
  rw [integral_Ioi_rpow_of_lt (by linarith : -s < -1) (by norm_num : (0 : ℝ)<1)] at htail
  have he : (∑' n : ℕ, (n : ℝ)^(-s))=1+∑' n : ℕ, ((n+1+1 : ℕ) : ℝ)^(-s) := by
    rw [← hsum.sum_add_tsum_nat_add 2]
    norm_num [Finset.sum_range_succ,show s≠0 by linarith]
    congr 1
    funext n
    congr 1
    ring
  rw [he]
  have htail' : (∑' n : ℕ, ((n+1+1 : ℕ) : ℝ)^(-s)) ≤ 1/(s-1) := by
    have hi : -(1 : ℝ)^(-s+1)/(-s+1)=1/(s-1) := by
      rw [Real.one_rpow,show -s+1= -(s-1) by ring]
      simp only [div_neg,neg_div,neg_neg]
    exact hi ▸ htail
  linarith

lemma finite_power_euler_product_le {s : ℝ} (hs : 1<s) (S : Finset ℕ) :
    (∏ p ∈ S.filter Nat.Prime, (1-(p : ℝ)^(-s))⁻¹) ≤ 1+1/(s-1) := by
  have hp : ∀ {p : ℕ}, p.Prime → ‖negativePower s p‖<1 := by
    intro p hp
    change ‖(p : ℝ)^(-s)‖<1
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    have h := Real.rpow_lt_rpow_of_exponent_lt (show (1 : ℝ)<p by exact_mod_cast hp.one_lt)
      (show -s<0 by linarith)
    simpa only [Real.rpow_zero] using h
  have he := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := negativePower s) hp S
  have hsum : Summable (fun n : ℕ => (n : ℝ)^(-s)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hb := hsum.tsum_subtype_le (fun n : ℕ => (n : ℝ)^(-s))
    (Nat.factoredNumbers S) (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have heq : (∑' n : Nat.factoredNumbers S, negativePower s n)=
      ∏ p ∈ S.filter Nat.Prime, (1-(p : ℝ)^(-s))⁻¹ := he.2.tsum_eq
  exact heq.symm.trans_le (hb.trans (negative_power_sum_le hs))

end TotientAsymptotic

end

end OAI
