import OAI.Analysis.LipschitzHilbert.Trees.SourceReferenceMask
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! The smallness of the actual top-mask derivative and Fourier radius
follows from packet shortness and the fixed narrow cone. All scale
parameters cancel before choosing the large manuscript parameter. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert.SlopeBox

theorem maskLineRate_packet_le (T : SlopeBox) (L A t ell cone : ℝ)
    (hL : 0 < L) (hell : 0 < ell) (hshort : ell ≤ T.length)
    (hcone : |t-T.slope| ≤ cone*T.width/ell) :
    2*(⌈L⌉₊:ℝ)*(|T.maskLineA L A|+|T.maskLineC L A t|) ≤
      (2*(⌈L⌉₊:ℝ)/L^A)*(1+cone)/ell := by
  have hx : 1/T.length ≤ 1/ell := one_div_le_one_div_of_le hell hshort
  have hy : |t-T.slope|/T.width ≤ cone/ell := by
    apply (div_le_iff₀ T.width_pos).mpr
    convert hcone using 1
    ring
  have hsum : 1/T.length+|t-T.slope|/T.width ≤ (1+cone)/ell := by
    calc
      _ ≤ 1/ell+cone/ell := add_le_add hx hy
      _ = _ := by ring
  unfold maskLineA maskLineC
  rw [abs_div,abs_div,abs_div,abs_div,abs_one,
    abs_of_pos T.length_pos,abs_of_pos T.width_pos,
    abs_of_pos (Real.rpow_pos_of_pos hL A)]
  calc
    _ = (2*(⌈L⌉₊:ℝ)/L^A)*(1/T.length+|t-T.slope|/T.width) := by ring
    _ ≤ (2*(⌈L⌉₊:ℝ)/L^A)*((1+cone)/ell) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

/-- A single scalar choice gives both derivative control and the
half-annulus margin, uniformly over top lengths and packet scales. -/
theorem scaled_maskLine_bounds (T : SlopeBox) (L A t ell cone r lo : ℝ)
    (hL : 0 < L) (hell : 0 < ell) (hr : 0 < r) (hshort : ell ≤ T.length)
    (hcone : |t-T.slope| ≤ cone*T.width/ell)
    (hsmall : (2*(⌈L⌉₊:ℝ)/L^A)*(1+cone) ≤ min 1 (Real.pi*lo)) :
    2*(⌈L⌉₊:ℝ)*(|r*T.maskLineA L A|+|r*T.maskLineC L A t|) ≤ 1/(ell/r) ∧
    (2*(⌈L⌉₊:ℝ))*((|r*T.maskLineA L A|+|r*T.maskLineC L A t|)/(2*Real.pi)) ≤
      (lo/2)/(ell/r) := by
  have hrate := T.maskLineRate_packet_le L A t ell cone hL hell hshort hcone
  have heq : 2*(⌈L⌉₊:ℝ)*(|r*T.maskLineA L A|+|r*T.maskLineC L A t|) =
      r*(2*(⌈L⌉₊:ℝ)*(|T.maskLineA L A|+|T.maskLineC L A t|)) := by
    rw [abs_mul,abs_mul,abs_of_pos hr]
    ring
  have hscaled := mul_le_mul_of_nonneg_left hrate hr.le
  have hfirst : r*(2*(⌈L⌉₊:ℝ)*(|T.maskLineA L A|+|T.maskLineC L A t|)) ≤ r/ell := by
    calc
      _ ≤ r*((2*(⌈L⌉₊:ℝ)/L^A)*(1+cone)/ell) := hscaled
      _ ≤ r*(1/ell) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (hsmall.trans (min_le_left _ _)) hell.le) hr.le
      _ = _ := by ring
  have hsecond : r*(2*(⌈L⌉₊:ℝ)*(|T.maskLineA L A|+|T.maskLineC L A t|)) ≤
      r*(Real.pi*lo)/ell := by
    calc
      _ ≤ r*((2*(⌈L⌉₊:ℝ)/L^A)*(1+cone)/ell) := hscaled
      _ ≤ r*((Real.pi*lo)/ell) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (hsmall.trans (min_le_right _ _)) hell.le) hr.le
      _ = _ := by ring
  constructor
  · rw [heq]
    convert hfirst using 1
    field_simp [hr.ne',hell.ne']
  · have h := (div_le_div_of_nonneg_right hsecond (by positivity : 0 ≤ 2*Real.pi))
    rw [← heq] at h
    convert h using 1 <;> field_simp [hr.ne',hell.ne',Real.pi_ne_zero]

/-- The source exponent A is fixed before choosing L. In particular no
factor involving the number or lengths of packets enters this choice. -/
theorem eventually_mask_scalar_small {A cone lo : ℝ} (hA : 1 < A)
    (hcone : 0 ≤ cone) (hlo : 0 < lo) :
    ∀ᶠ L : ℝ in atTop,
      (2*(⌈L⌉₊:ℝ)/L^A)*(1+cone) ≤ min 1 (Real.pi*lo) := by
  let eps := min 1 (Real.pi*lo)
  have heps : 0 < eps := lt_min (by norm_num) (mul_pos Real.pi_pos hlo)
  filter_upwards [eventually_ge_atTop (1:ℝ),
    (tendsto_rpow_atTop (sub_pos.mpr hA)).eventually_ge_atTop (4*(1+cone)/eps)]
    with L hL hpow
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hceil : (⌈L⌉₊:ℝ) ≤ 2*L := by
    have h := (Nat.ceil_lt_add_one hL0.le).le
    linarith
  have hLp : 0 < L^(A-1) := Real.rpow_pos_of_pos hL0 _
  have hbudget : 4*(1+cone) ≤ eps*L^(A-1) := by
    have h := (div_le_iff₀ heps).mp hpow
    simpa only [mul_comm] using h
  have hpower : L^A = L*L^(A-1) := by
    calc
      _ = L^(1+(A-1)) := by congr 1; ring
      _ = L^1*L^(A-1) := Real.rpow_add hL0 _ _
      _ = _ := by rw [Real.rpow_one]
  change _ ≤ eps
  calc
    _ ≤ (2*(2*L)/L^A)*(1+cone) := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hceil (by norm_num))
        (Real.rpow_nonneg hL0.le _)) (by linarith)
    _ = (4*(1+cone))/L^(A-1) := by rw [hpower]; field_simp; ring
    _ ≤ eps := (div_le_iff₀ hLp).mpr hbudget

end LipschitzHilbert.SlopeBox

end

end OAI
