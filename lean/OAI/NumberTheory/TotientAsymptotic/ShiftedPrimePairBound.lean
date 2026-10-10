import OAI.NumberTheory.TotientAsymptotic.SieveEulerProduct
import OAI.NumberTheory.TotientAsymptotic.ShiftedSieveError
import OAI.NumberTheory.TotientAsymptotic.TotientRatioLogLog

namespace OAI

/-! The two-linear-form upper bound with all Selberg quantities eliminated. -/
noncomputable section
open scoped BigOperators
open SelbergSieve
namespace TotientAsymptotic

 theorem shiftedPrimePairs_log_bound {b : ℕ} (hb : 0<b) (X z : ℕ)
    (y : ℝ) (hy : 1<y) (hz : 2≤z)
    (hscale : 8*Real.log 4*(2+Real.log z) ≤ Real.log y) :
    ((shiftedPrimePairs b X z).card:ℝ) ≤
      8*X*((b:ℝ)/b.totient)/(Real.log z)^2+2*y^3 := by
  let s := shiftedPrimeSieve b X z y hy.le
  let P := ∏ p ∈ oddSievePrimes z,(1+shiftedSieveWeight b p)
  let R : ℝ := (b:ℝ)/b.totient
  have hR : 0≤R := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hD : 0<selbergBoundingSum s := selbergBoundingSum_pos s
  have hlog : 0<Real.log z := Real.log_pos (by exact_mod_cast (show 1<z by omega))
  have hP : P/2 ≤ selbergBoundingSum s := shiftedSieveBoundingSum_lower b X z y hy hz hscale
  have hprod : (Real.log z)^2/4 ≤ P*R := shiftedSieveEulerProduct_lower hb z hz
  have hden : (Real.log z)^2 ≤ 8*selbergBoundingSum s*R := by
    have hh := mul_le_mul_of_nonneg_right hP hR
    nlinarith
  have hmain : (X:ℝ)/selbergBoundingSum s ≤ 8*X*R/(Real.log z)^2 := by
    apply (div_le_div_iff₀ hD (sq_pos_of_pos hlog)).mpr
    have hh := mul_le_mul_of_nonneg_left hden (Nat.cast_nonneg X : (0:ℝ)≤X)
    nlinarith
  exact (shiftedPrimePairs_bound b X z y hy.le).trans (add_le_add hmain le_rfl)

end TotientAsymptotic

end

end OAI
