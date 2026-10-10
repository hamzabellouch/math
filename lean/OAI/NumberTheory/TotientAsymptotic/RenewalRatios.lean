import OAI.NumberTheory.TotientAsymptotic.RenewalInput
import OAI.NumberTheory.TotientAsymptotic.RenewalLower

namespace OAI

/-! Uniform coefficient ratios for the simplex coordinate estimates. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma renewal_ratio_error : ∃ C : ℝ, 0<C ∧ ∀ i k : ℕ,
    |g k/(rho^i*g (i+k))-1|≤C*rho^k := by
  obtain ⟨E,hE,he⟩ := fordRenewalInput
  obtain ⟨c,hc,hg⟩ := renewal_uniform_lower fordRenewalInput
  refine ⟨2*(E+1)/c,by positivity,?_⟩
  intro i k
  have hr : 0<rho^i := pow_pos rho_pos i
  have hrk : 0<rho^k := pow_pos rho_pos k
  have hi1 : rho^i≤1 := pow_le_one₀ rho_pos.le rho_lt_one.le
  have hD : 0<rho^i*g (i+k) := mul_pos hr (g_pos _)
  have hnorm : |g k-rho^i*g (i+k)|≤2*(E+1) := by
    have hid : g k-rho^i*g (i+k)=
        (g k-gamma*(rho^k)⁻¹)-rho^i*(g (i+k)-gamma*(rho^(i+k))⁻¹) := by
      rw [pow_add]
      field_simp [hr.ne',hrk.ne']
      ring
    rw [hid]
    calc
      _ ≤ |g k-gamma*(rho^k)⁻¹|+|rho^i*(g (i+k)-gamma*(rho^(i+k))⁻¹)| := abs_sub _ _
      _ ≤ E+rho^i*E := by
        rw [abs_mul,abs_of_pos hr]
        exact add_le_add (he k) (mul_le_mul_of_nonneg_left (he (i+k)) hr.le)
      _ ≤ 2*(E+1) := by nlinarith
  have hden : c*(rho^k)⁻¹≤rho^i*g (i+k) := by
    have hh := mul_le_mul_of_nonneg_left (hg (i+k)) hr.le
    convert hh using 1
    rw [pow_add]
    field_simp [hr.ne',hrk.ne']
  have hi : (rho^i*g (i+k))⁻¹≤rho^k/c := by
    have hh := inv_anti₀ (mul_pos hc (inv_pos.mpr hrk)) hden
    convert hh using 1
    simp only [mul_inv_rev,inv_inv,div_eq_mul_inv]
  have hid : g k/(rho^i*g (i+k))-1=(g k-rho^i*g (i+k))/(rho^i*g (i+k)) := by
    field_simp [hD.ne', (g_pos (i+k)).ne', hr.ne']
  rw [hid,abs_div,abs_of_pos hD,div_eq_mul_inv]
  calc
    _ ≤ 2*(E+1)*(rho^k/c) := mul_le_mul hnorm hi (inv_pos.mpr hD).le (by positivity)
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
