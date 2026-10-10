import OAI.Geometry.Kahler.BasePeakBounds

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma chart_small_ball {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    {z : Base} (hz : ‖z‖ < (1/32:ℝ)) :
    1/2 ≤ ‖1+(r:ℂ)*z 0‖ ∧ ‖1+(r:ℂ)*z 0‖ ≤ 2 := by
  have hz0 := PiLp.norm_apply_le (p := (2:ENNReal)) z 0
  have hm : ‖(r:ℂ)*z 0‖ ≤ 1/32 := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr]
    have := norm_nonneg (z 0)
    nlinarith
  have hupper := norm_add_le (1:ℂ) ((r:ℂ)*z 0)
  have hlower := norm_add_le (1+(r:ℂ)*z 0) (-((r:ℂ)*z 0))
  simp only [norm_one] at hupper
  simp only [add_neg_cancel_right,norm_one,norm_neg] at hlower
  constructor <;> linarith

lemma chart_norm_deficit {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (U : Base ≃ₗᵢ[ℂ] Base) {z : Base} (hz : ‖z‖ < (1/32:ℝ)) :
    ‖centeredChart r U z‖ ≤ 1-(1-r)/16 := by
  have hzb : z ∈ ball := by change ‖z‖ < 1; linarith
  have hd := centeredChart_den_ne_zero hr hr1 hzb
  have he := centeredChart_norm_identity hr hr1 U z hd
  have hnorm : ‖centeredChart r U z‖ < 1 := centeredChart_mapsTo hr hr1 U hzb
  have hden := chart_small_ball hr hr1 hz
  have hsqden : ‖1+(r:ℂ)*z 0‖^2 ≤ 4 := by nlinarith [norm_nonneg (1+(r:ℂ)*z 0)]
  have hnum : (1-r)/2 ≤ (1-r^2)*(1-‖z‖^2) := by
    have hn : ‖z‖^2 ≤ 1/2 := by nlinarith [norm_nonneg z]
    have hrr : 1-r ≤ 1-r^2 := by nlinarith
    nlinarith
  have hdiv : (1-r)/8 ≤ (1-r^2)*(1-‖z‖^2)/‖1+(r:ℂ)*z 0‖^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos (by linarith : 0 < ‖1+(r:ℂ)*z 0‖))).2
    nlinarith
  rw [← he] at hdiv
  nlinarith [norm_nonneg (centeredChart r U z)]

lemma peak_chart_high {D : ℝ} (hD : 1 ≤ D) {k : ℕ} (hk : 1 ≤ k)
    {P : Finset Sphere} (hP : ProjectivelySeparated (D/Real.sqrt k) P)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (U : Base ≃ₗᵢ[ℂ] Base)
    {z : Base} (hz : ‖z‖ < (1/32:ℝ)) :
    ‖peakPolynomial P k (centeredChart r U z)‖ ≤ gaussianConstant*Real.exp (-(k:ℝ)*(1-r)/16) := by
  have hb := chart_norm_deficit hr hr1 U hz
  have he : ‖centeredChart r U z‖ ≤ Real.exp (-(1-r)/16) :=
    hb.trans (by simpa only [neg_div] using Real.one_sub_le_exp_neg ((1-r)/16))
  have hp := pow_le_pow_left₀ (norm_nonneg (centeredChart r U z)) he k
  rw [← Real.exp_nat_mul] at hp
  have hex : (k:ℝ)*(-(1-r)/16)=-(k:ℝ)*(1-r)/16 := by ring
  rw [hex] at hp
  exact (peak_global_bound hD hk hP _).trans (mul_le_mul_of_nonneg_left hp gaussianConstant_pos.le)

end PinchedHartogs.BaseConstruction

end

end OAI
