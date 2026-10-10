import OAI.Analysis.LipschitzHilbert.Estimates.DyadicErrorProfile

namespace OAI

/-! Pointwise source and source-sum estimates for the manuscript's
annular indicator plus small-angle error profile. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

theorem sum_dyadic_small_ratio (N : ℕ) (a c v : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hv : 0 ≤ v) :
    (∑ j : Fin N, if v ≤ c*(a*(2 : ℝ)^j.val) then v/(a*(2 : ℝ)^j.val) else 0) ≤ 4*c := by
  by_cases hv0 : v = 0
  · simp only [hv0, zero_div, ite_self, Finset.sum_const_zero]
    positivity
  have hvp : 0 < v := lt_of_le_of_ne hv (Ne.symm hv0)
  have hr : 0 < v/(2*c) := div_pos hvp (by positivity)
  have hpoint (j : Fin N) :
      (if v ≤ c*(a*(2 : ℝ)^j.val) then v/(a*(2 : ℝ)^j.val) else 0) ≤
        v * (if v/(2*c) < a*(2 : ℝ)^j.val then (a*(2 : ℝ)^j.val)⁻¹ else 0) := by
    have hd : 0 < a*(2 : ℝ)^j.val := by positivity
    by_cases hj : v ≤ c*(a*(2 : ℝ)^j.val)
    · have hlt : v/(2*c) < a*(2 : ℝ)^j.val := by
        apply (div_lt_iff₀ (by positivity : 0 < 2*c)).mpr
        nlinarith
      rw [ite_eq_left hj, ite_eq_left hlt, div_eq_mul_inv]
    · simp only [ite_eq_right hj]
      split_ifs <;> positivity
  calc
    _ ≤ ∑ j : Fin N, v * (if v/(2*c) < a*(2 : ℝ)^j.val then (a*(2 : ℝ)^j.val)⁻¹ else 0) :=
      Finset.sum_le_sum (fun j _ => hpoint j)
    _ = v * ∑ j : Fin N, if v/(2*c) < a*(2 : ℝ)^j.val then (a*(2 : ℝ)^j.val)⁻¹ else 0 :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ v * (2/(v/(2*c))) :=
      mul_le_mul_of_nonneg_left (sum_large_increasing_dyadic_reciprocals N a (v/(2*c)) ha hr) hv
    _ = 4*c := by field_simp; norm_num

def dyadicErrorSource (c : ℝ) (K : ℕ) (d v : ℝ) : ℝ :=
  (if c*d ≤ v ∧ v ≤ (2 : ℝ)^K * (c*d) then 1 else 0) +
    (if v ≤ c*d then v/d else 0)

theorem dyadicErrorSource_bounds (c : ℝ) (K : ℕ) (d v : ℝ)
    (hc : 0 < c) (hd : 0 < d) (hv : 0 ≤ v) :
    0 ≤ dyadicErrorSource c K d v ∧ dyadicErrorSource c K d v ≤ 1+c := by
  have ht : 0 ≤ (if v ≤ c*d then v/d else 0) ∧ (if v ≤ c*d then v/d else 0) ≤ c := by
    by_cases h : v ≤ c*d
    · simp only [ite_eq_left h]
      exact ⟨div_nonneg hv hd.le, (div_le_iff₀ hd).mpr h⟩
    · simp only [ite_eq_right h]
      exact ⟨le_rfl,hc.le⟩
  have hfirst : 0 ≤ (if c*d ≤ v ∧ v ≤ (2 : ℝ)^K*(c*d) then (1 : ℝ) else 0) ∧
      (if c*d ≤ v ∧ v ≤ (2 : ℝ)^K*(c*d) then (1 : ℝ) else 0) ≤ 1 := by
    split_ifs <;> constructor <;> norm_num
  exact ⟨add_nonneg hfirst.1 ht.1, add_le_add hfirst.2 ht.2⟩

theorem sum_dyadicErrorSource (N K : ℕ) (a c v : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hv : 0 ≤ v) :
    (∑ j : Fin N, dyadicErrorSource c K (a*(2 : ℝ)^j.val) v) ≤ (K+1 : ℕ) + 4*c := by
  have heq (j : Fin N) : c*(a*(2 : ℝ)^j.val) = (c*a)*(2 : ℝ)^j.val := by ring
  have hcount : (∑ j : Fin N, if c*(a*(2 : ℝ)^j.val) ≤ v ∧
      v ≤ (2 : ℝ)^K * (c*(a*(2 : ℝ)^j.val)) then (1 : ℝ) else 0) ≤ (K+1 : ℕ) := by
    simp_rw [heq]
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast dyadic_band_card N K (c*a) v (mul_pos hc ha)
  have htail := sum_dyadic_small_ratio N a c v ha hc hv
  simp only [dyadicErrorSource, Finset.sum_add_distrib]
  linarith

end LipschitzHilbert

end

end OAI
