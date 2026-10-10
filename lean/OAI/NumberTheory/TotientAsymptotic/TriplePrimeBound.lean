import OAI.NumberTheory.TotientAsymptotic.TripleEulerProduct
import OAI.NumberTheory.TotientAsymptotic.TripleSieveError

namespace OAI

/-! Elimination of Selberg's auxiliary quantities in the three-form bound. -/
noncomputable section
open scoped BigOperators
open SelbergSieve
namespace TotientAsymptotic

lemma triplePrimeTuples_log_bound {a b : ℕ} (ha : 0 < a) (hab : a < b) (X z : ℕ)
    (y : ℝ) (hy : 1 < y) (hz : 3 ≤ z)
    (hscale : 12*Real.log 4*(2+Real.log z) ≤ Real.log y) :
    ((triplePrimeTuples a b X z).card:ℝ) ≤
      54*X*((tripleDiscriminant a b:ℝ)/(tripleDiscriminant a b).totient)^2/(Real.log z)^3+2*y^3 := by
  let s := triplePrimeSieve a b X z y hy.le
  let P := ∏ p ∈ tripleSievePrimes z,(1+tripleSieveWeight a b p)
  let R : ℝ := ((tripleDiscriminant a b:ℝ)/(tripleDiscriminant a b).totient)^2
  have hR : 0 ≤ R := sq_nonneg _
  have hD : 0 < selbergBoundingSum s := selbergBoundingSum_pos s
  have hlog : 0 < Real.log z := Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have hP : P/2 ≤ selbergBoundingSum s :=
    tripleSieveBoundingSum_lower a b X z y hy (by omega) hscale
  have hprod : (Real.log z)^3/27 ≤ P*R := tripleSieveEulerProduct_lower ha hab z hz
  have hden : (Real.log z)^3 ≤ 54*selbergBoundingSum s*R := by
    have hh := mul_le_mul_of_nonneg_right hP hR
    nlinarith
  have hmain : (X:ℝ)/selbergBoundingSum s ≤ 54*X*R/(Real.log z)^3 := by
    apply (div_le_div_iff₀ hD (pow_pos hlog 3)).mpr
    have hh := mul_le_mul_of_nonneg_left hden (Nat.cast_nonneg X : (0:ℝ) ≤ X)
    nlinarith
  exact (triplePrimeTuples_bound a b X z y hy.le).trans (add_le_add hmain le_rfl)

end TotientAsymptotic

end

end OAI
