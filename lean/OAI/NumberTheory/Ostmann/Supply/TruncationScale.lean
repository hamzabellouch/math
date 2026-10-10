import OAI.NumberTheory.Ostmann.Supply.RetainedBandScales
import OAI.NumberTheory.Ostmann.Supply.UnitWeightTruncation

namespace OAI

noncomputable section
namespace Ostmann.Supply
open Filter
open scoped BigOperators

theorem supplyTruncation_ge (L : ℝ) : 10000*L≤(supplyTruncation L:ℝ) :=
  Nat.le_ceil _

theorem supply_inverse_radius_power_le {L : ℝ} (_hL : 0≤L) :
    ((103/100:ℝ)⁻¹)^(supplyTruncation L)≤Real.exp (-100*L) := by
  have hlog : (1/100:ℝ)≤Real.log (103/100) := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<103/100)
    norm_num at h ⊢
    linarith
  have hk := supplyTruncation_ge L
  have hk0 : (0:ℝ)≤ supplyTruncation L := Nat.cast_nonneg _
  rw [←Real.exp_log (by norm_num : (0:ℝ)<(103/100:ℝ)⁻¹),←Real.exp_nat_mul,
    Real.log_inv]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem supply_tail_le {L H C : ℝ} (hL : 0≤L) (hH : H≤L)
    (hC : 0≤C) (hC3 : C≤3) :
    2*Real.exp (C*H)*((103/100:ℝ)⁻¹)^(supplyTruncation L)/
      (1-(103/100:ℝ)⁻¹)^2≤2400*Real.exp (-97*L) := by
  have hCH : C*H≤3*L := (mul_le_mul_of_nonneg_left hH hC).trans
    (mul_le_mul_of_nonneg_right hC3 hL)
  have hmul := mul_le_mul (Real.exp_le_exp.mpr hCH)
    (supply_inverse_radius_power_le hL) (by positivity) (Real.exp_pos _).le
  have he : Real.exp (3*L)*Real.exp (-100*L)=Real.exp (-97*L) := by
    rw [←Real.exp_add]
    congr 1
    ring
  rw [he] at hmul
  have hh := mul_le_mul_of_nonneg_left hmul
    (by norm_num : (0:ℝ)≤2/(1-(103/100:ℝ)⁻¹)^2)
  calc
    _ ≤ (2/(1-(103/100:ℝ)⁻¹)^2)*Real.exp (-97*L) := by
      convert hh using 1
      ring
    _ ≤ 2400*Real.exp (-97*L) := by gcongr; norm_num

theorem eventually_supply_tail_small :
    ∀ᶠL:ℝ in atTop, ∀H C:ℝ, H≤L → 0≤C → C≤3 →
      2*Real.exp (C*H)*((103/100:ℝ)⁻¹)^(supplyTruncation L)/
        (1-(103/100:ℝ)⁻¹)^2≤Real.exp (-10*L) := by
  have hh : ∀ᶠL:ℝ in atTop, (2400:ℝ)≤Real.exp (87*L) :=
    (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))).eventually
      (eventually_ge_atTop _)
  filter_upwards [hh,eventually_ge_atTop (0:ℝ)] with L hh hL
  intro H C hH hC hC3
  apply (supply_tail_le hL hH hC hC3).trans
  calc
    _ ≤ Real.exp (87*L)*Real.exp (-97*L) := mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le
    _ = Real.exp (-10*L) := by rw [←Real.exp_add]; congr 1; ring

end Ostmann.Supply

end

end OAI
