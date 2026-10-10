import Mathlib

namespace OAI

                                     
section

/-! Exact held side parameters and their uniform logarithmic bounds, companion
 §04. No lower bound on a side proportion and no cardinality factor is used. -/
namespace UniformKServer.SideParameters
noncomputable section

def height (A a : ℝ) : ℝ := 1+Real.log (A/a)
def offset (A a : ℝ) : ℝ := a/(A*height A a)
def slack (ell cw A a : ℝ) : ℝ := cw*height A a/ell

theorem height_ge_one {A a : ℝ} (ha : 0 < a) (haA : a ≤ A) : 1 ≤ height A a := by
  unfold height
  have h := Real.log_nonneg ((one_le_div ha).mpr haA)
  linarith

theorem offset_pos {A a : ℝ} (ha : 0 < a) (haA : a ≤ A) : 0 < offset A a := by
  have hA : 0 < A := ha.trans_le haA
  have hh : 0 < height A a := lt_of_lt_of_le zero_lt_one (height_ge_one ha haA)
  exact div_pos ha (mul_pos hA hh)

theorem offset_inverse {A a : ℝ} (ha : 0 < a) (haA : a ≤ A) :
    1/offset A a = height A a*(A/a) := by
  have hA : 0 < A := ha.trans_le haA
  have hh : 0 < height A a := lt_of_lt_of_le zero_lt_one (height_ge_one ha haA)
  unfold offset
  field_simp

/-- The side logarithm is at most (W+2)h throughout its compact domain. -/
theorem log_bound {A a s W : ℝ} (ha : 0 < a) (haA : a ≤ A)
    (hs : 0 ≤ s) (hsW : s ≤ W) :
    Real.log (1+s/offset A a) ≤ (W+2)*height A a := by
  have hA : 0 < A := ha.trans_le haA
  have hh := height_ge_one ha haA
  have hh₀ : 0 < height A a := by linarith
  have hz := offset_pos ha haA
  have hq : 1 ≤ A/a := (one_le_div ha).mpr haA
  have hp : 1 ≤ height A a*(A/a) := one_le_mul_of_one_le_of_one_le hh hq
  have ht : 1+s/offset A a ≤ (1+s)*height A a*(A/a) := by
    rw [div_eq_mul_one_div s,offset_inverse ha haA]
    nlinarith
  have hl := Real.log_le_log (by positivity : 0 < 1+s/offset A a) ht
  rw [Real.log_mul (by positivity : (1+s)*height A a ≠ 0) (div_pos hA ha).ne',
    Real.log_mul (by positivity : 1+s ≠ 0) hh₀.ne'] at hl
  have hl₁ := Real.log_le_sub_one_of_pos (by positivity : 0 < 1+s)
  have hl₂ := Real.log_le_sub_one_of_pos hh₀
  have he : Real.log (A/a)=height A a-1 := by unfold height; ring
  rw [he] at hl
  have hW : 0 ≤ W := hs.trans hsW
  nlinarith

theorem slack_pos {ell cw A a : ℝ} (hell : 0 < ell) (hcw : 0 < cw)
    (ha : 0 < a) (haA : a ≤ A) : 0 < slack ell cw A a := by
  have hh : 0 < height A a := lt_of_lt_of_le zero_lt_one (height_ge_one ha haA)
  exact div_pos (mul_pos hcw hh) hell

theorem inverse_slack {ell cw A a : ℝ} (hell : 0 < ell) (hcw : 0 < cw)
    (ha : 0 < a) (haA : a ≤ A) :
    1/slack ell cw A a ≤ ell/cw := by
  have hh := height_ge_one ha haA
  have hh₀ : 0 < height A a := by linarith
  unfold slack
  rw [one_div_div]
  apply div_le_div_of_nonneg_left hell.le hcw
  nlinarith

theorem logarithm_over_slack {ell cw A a s W : ℝ} (hell : 0 < ell) (hcw : 0 < cw)
    (ha : 0 < a) (haA : a ≤ A) (hs : 0 ≤ s) (hsW : s ≤ W) :
    Real.log (1+s/offset A a)/slack ell cw A a ≤ (W+2)*ell/cw := by
  have hh₀ : 0 < height A a := lt_of_lt_of_le zero_lt_one (height_ge_one ha haA)
  have hslack := slack_pos hell hcw ha haA
  apply (div_le_iff₀ hslack).mpr
  calc
    _ ≤ (W+2)*height A a := log_bound ha haA hs hsW
    _ = _ := by unfold slack; field_simp

end
end UniformKServer.SideParameters

end

end OAI
