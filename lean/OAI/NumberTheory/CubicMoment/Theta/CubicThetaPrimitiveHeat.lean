import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimitiveKernel
import OAI.NumberTheory.CubicMoment.Estimates.RieszHeatKernel
import OAI.NumberTheory.CubicMoment.Estimates.ThetaHeatKernelBound
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! The actual positive heat representation of the truncated primitive kernel. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment
local instance : Countable Eisenstein := coordinatesEquiv.symm.injective.countable
local instance : Countable CubicThetaPrimitiveRow := by
  have hi : Function.Injective (fun r : CubicThetaPrimitiveRow => (r.c,r.d)) := by
    intro r s h
    exact CubicThetaPrimitiveRow.ext (Prod.mk.inj h).1 (Prod.mk.inj h).2
  exact hi.countable

def cubicThetaPrimitiveHeatTerm (p : ℂ × ℝ) (t : ℝ) (r : CubicThetaPrimitiveRow) : ℝ :=
  if r.height p≤1 then Real.exp (-t/r.height p) else 0

def cubicThetaPrimitiveHeat (p : ℂ × ℝ) (t : ℝ) : ℝ :=
  ∑' r : CubicThetaPrimitiveRow,cubicThetaPrimitiveHeatTerm p t r

lemma cubicThetaPrimitiveHeatTerm_nonneg (p : ℂ × ℝ) (t : ℝ) (r : CubicThetaPrimitiveRow) :
    0≤cubicThetaPrimitiveHeatTerm p t r := by
  unfold cubicThetaPrimitiveHeatTerm
  split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl

lemma cubicThetaPrimitiveHeat_summable {p : ℂ × ℝ} (hp : 0<p.2)
    {t : ℝ} (ht : 0<t) : Summable (cubicThetaPrimitiveHeatTerm p t) := by
  have hsum := (cubicThetaPrimitiveHeight_summable hp (s:=3) (by norm_num)).mul_left (6/t^3)
  apply hsum.of_nonneg_of_le (cubicThetaPrimitiveHeatTerm_nonneg p t)
  intro r
  unfold cubicThetaPrimitiveHeatTerm
  split_ifs
  · have hx := r.height_pos hp
    have hi := power_exp_bound ht 3 (r.height p)⁻¹ (inv_pos.mpr hx).le
    norm_num only [Nat.factorial_succ,Nat.factorial_zero,Nat.cast_mul,Nat.cast_one,
      Nat.cast_ofNat,mul_one] at hi
    rw [Real.rpow_ofNat]
    have hh : Real.exp (-t/r.height p)=Real.exp (-t*(r.height p)⁻¹) := by rw [div_eq_mul_inv]
    rw [hh]
    apply (div_le_iff₀ (pow_pos hx 3)).mp
    simpa only [div_eq_mul_inv,inv_pow,mul_comm] using hi
  · exact mul_nonneg (by positivity) (Real.rpow_nonneg (r.height_pos hp).le _)

def cubicThetaPrimitiveHeatMellinTerm (p : ℂ × ℝ) (s : ℝ)
    (r : CubicThetaPrimitiveRow) (t : ℝ) : ℝ :=
  t^(s-1)*cubicThetaPrimitiveHeatTerm p t r

lemma cubicThetaPrimitiveHeatMellinTerm_integrable {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℝ} (hs : 0<s) (r : CubicThetaPrimitiveRow) :
    IntegrableOn (cubicThetaPrimitiveHeatMellinTerm p s r) (Ioi 0) := by
  unfold cubicThetaPrimitiveHeatMellinTerm cubicThetaPrimitiveHeatTerm
  by_cases hr : r.height p≤1
  · simp only [ite_eq_left hr]
    convert integrable_laplace_rpow hs (inv_pos.mpr (r.height_pos hp)) using 1
    funext t
    congr 2
    rw [div_eq_mul_inv]
    ring
  · simp only [ite_eq_right hr,mul_zero]
    exact integrableOn_zero

lemma cubicThetaPrimitiveHeatMellinTerm_integral {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℝ} (hs : 0<s) (r : CubicThetaPrimitiveRow) :
    (∫ t in Ioi (0:ℝ),cubicThetaPrimitiveHeatMellinTerm p s r t)=
      Real.Gamma s*(if r.height p≤1 then r.height p^s else 0) := by
  unfold cubicThetaPrimitiveHeatMellinTerm cubicThetaPrimitiveHeatTerm
  by_cases hr : r.height p≤1
  · simp only [ite_eq_left hr]
    have he : ∀ t : ℝ,-t/r.height p= -(r.height p)⁻¹*t := by intro t; rw [div_eq_mul_inv]; ring
    simp_rw [he]
    rw [laplace_rpow hs (inv_pos.mpr (r.height_pos hp)),
      Real.inv_rpow (r.height_pos hp).le,Real.rpow_neg (r.height_pos hp).le,inv_inv]
  · simp only [ite_eq_right hr,mul_zero,integral_zero]

lemma cubicThetaPrimitiveHeatMellinTerm_mass {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℝ} (hs : 0<s) (r : CubicThetaPrimitiveRow) :
    (∫ t in Ioi (0:ℝ),‖cubicThetaPrimitiveHeatMellinTerm p s r t‖)=
      Real.Gamma s*(if r.height p≤1 then r.height p^s else 0) := by
  rw [←cubicThetaPrimitiveHeatMellinTerm_integral hp hs r]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  exact Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _)
    (cubicThetaPrimitiveHeatTerm_nonneg p t r))

theorem cubicThetaPrimitiveKernel_heat_mellin {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℝ} (hs : 2<s) :
    (∫ t in Ioi (0:ℝ),t^(s-1)*cubicThetaPrimitiveHeat p t)=
      Real.Gamma s*cubicThetaPrimitiveKernel p s := by
  have hs0 : 0<s := lt_trans (by norm_num) hs
  have hmass : Summable (fun r : CubicThetaPrimitiveRow =>
      ∫ t in Ioi (0:ℝ),‖cubicThetaPrimitiveHeatMellinTerm p s r t‖) := by
    simp_rw [cubicThetaPrimitiveHeatMellinTerm_mass hp hs0]
    exact (cubicThetaPrimitiveKernel_summable hp hs).mul_left _
  calc
    _ = ∫ t in Ioi (0:ℝ),∑' r : CubicThetaPrimitiveRow,cubicThetaPrimitiveHeatMellinTerm p s r t := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      dsimp only
      rw [cubicThetaPrimitiveHeat,←tsum_mul_left]
      rfl
    _ = ∑' r : CubicThetaPrimitiveRow,∫ t in Ioi (0:ℝ),cubicThetaPrimitiveHeatMellinTerm p s r t :=
      (integral_tsum_of_summable_integral_norm
        (fun r => cubicThetaPrimitiveHeatMellinTerm_integrable hp hs0 r) hmass).symm
    _ = _ := by
      simp_rw [cubicThetaPrimitiveHeatMellinTerm_integral hp hs0]
      rw [tsum_mul_left]
      rfl

end CubicFirstMoment

end

end OAI
