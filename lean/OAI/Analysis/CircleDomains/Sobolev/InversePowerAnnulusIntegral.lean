import OAI.Analysis.CircleDomains.Sobolev.ExteriorAnnulusEnergy
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace OAI

/-! The exact radial integral of each Laurent coefficient's energy. -/
open Set Filter Function Metric Real MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma integral_radial_inverse_power {a b : ℝ} (ha : 0 < a) (hab : a < b) (n : ℕ) :
    (∫ r in Ioo a b, r*(r⁻¹)^(2*(n+2))) =
      ((a⁻¹)^(2*(n+1))-(b⁻¹)^(2*(n+1))) / (2*((n : ℝ)+1)) := by
  have hn : (2*(n+2)) = (2*(n+1)+1)+1 := by omega
  have he (r : ℝ) (hr : r ≠ 0) : r*(r⁻¹)^(2*(n+2)) =
      r^(-((2*(n+1)+1 : ℕ) : ℤ)) := by
    rw [zpow_neg, zpow_natCast, inv_pow, hn, pow_succ]
    field_simp
  have hzero : (0 : ℝ) ∉ Set.uIcc a b := by
    rw [uIcc_of_le hab.le]
    intro h
    exact ha.not_ge h.1
  have h := integral_zpow (a := a) (b := b)
    (n := -((2*(n+1)+1 : ℕ) : ℤ)) (Or.inr ⟨by omega, hzero⟩)
  have hexp : -((2*(n+1)+1 : ℕ) : ℤ)+1 = -((2*(n+1) : ℕ) : ℤ) := by omega
  rw [hexp, zpow_neg, zpow_natCast, zpow_neg, zpow_natCast] at h
  push_cast at h
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab.le]
  calc
    _ = ∫ r in a..b, r^(-((2*(n+1)+1 : ℕ) : ℤ)) := by
      apply intervalIntegral.integral_congr
      intro r hr
      exact he r (ne_of_gt (ha.trans_le ((uIcc_of_le hab.le ▸ hr).1)))
    _ = _ := by
      push_cast
      rw [h, inv_pow, inv_pow]
      have hn0 : (n : ℝ)+1 ≠ 0 := by positivity
      field_simp
      ring

end CircleDomainRigidity

end

end OAI
