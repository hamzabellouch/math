import OAI.NumberTheory.Ostmann.Supply.NaturalWeight
import OAI.NumberTheory.Ostmann.Supply.RetainedBandScales

namespace OAI

noncomputable section
namespace Ostmann.Supply
open Filter

theorem exp_le_supply_square_log (L : ℝ) :
    Real.exp L ≤ Real.log (((supplyRadius L)^2:ℕ):ℝ) := by
  have hR : Real.exp (Real.exp L/2) ≤ (supplyRadius L:ℝ) := Nat.le_ceil _
  have hpos : (0:ℝ)<supplyRadius L := Nat.cast_pos.mpr (supplyRadius_pos L)
  have hlog := Real.log_le_log (Real.exp_pos (Real.exp L/2)) hR
  rw [Real.log_exp] at hlog
  rw [Nat.cast_pow,Real.log_pow]
  norm_num
  linarith

theorem supply_square_tendsto : Tendsto (fun L => (supplyRadius L)^2) atTop atTop := by
  exact (tendsto_pow_atTop (by decide : (2:ℕ)≠0)).comp supplyRadius_tendsto

theorem eventually_boundary_weight_bound :
    ∀ᶠ L : ℝ in atTop, ∀ n : ℕ,
      (n:ℝ) ≤ Real.exp (Real.exp ((9/10:ℝ)*L)) →
      (supplyTruncation L+1:ℝ)^2*(n+1:ℝ)^(2*supplyTruncation L) ≤
        ((((supplyRadius L)^2:ℕ):ℝ))^(1/100:ℝ) := by
  filter_upwards [eventually_supplyTruncation_le_exp
    (by norm_num : (0:ℝ)<1/10) (by norm_num : (0:ℝ)<1/300),
    eventually_ge_atTop (0:ℝ)] with L hK hL
  intro n hn
  have hy : 1 ≤ Real.exp ((9/10:ℝ)*L) := Real.one_le_exp (by positivity)
  have he : 2 ≤ Real.exp (Real.exp ((9/10:ℝ)*L)) := by
    have := Real.add_one_le_exp (Real.exp ((9/10:ℝ)*L))
    linarith
  have hnbase : (n+1:ℝ) ≤ Real.exp (2*Real.exp ((9/10:ℝ)*L)) := by
    rw [show 2*Real.exp ((9/10:ℝ)*L)=
      Real.exp ((9/10:ℝ)*L)+Real.exp ((9/10:ℝ)*L) by ring,Real.exp_add]
    nlinarith
  have hkbase : (supplyTruncation L+1:ℝ) ≤ Real.exp (supplyTruncation L:ℝ) :=
    Real.add_one_le_exp _
  have hwp := mul_le_mul (pow_le_pow_left₀ (by positivity) hkbase 2)
    (pow_le_pow_left₀ (by positivity) hnbase (2*supplyTruncation L)) (by positivity) (by positivity)
  have hex : Real.exp (supplyTruncation L:ℝ)^2 *
      Real.exp (2*Real.exp ((9/10:ℝ)*L))^(2*supplyTruncation L) =
      Real.exp ((2*supplyTruncation L:ℕ)*(1+2*Real.exp ((9/10:ℝ)*L))) := by
    rw [←Real.exp_nat_mul,←Real.exp_nat_mul,←Real.exp_add]
    congr 1
    push_cast
    ring
  rw [hex] at hwp
  have hprod := mul_le_mul_of_nonneg_right hK (by positivity : 0≤3*Real.exp ((9/10:ℝ)*L))
  have hexprod : ((1/300:ℝ)*Real.exp ((1/10:ℝ)*L)) *
      (3*Real.exp ((9/10:ℝ)*L)) = (1/100:ℝ)*Real.exp L := by
    have heq : Real.exp ((1/10:ℝ)*L)*Real.exp ((9/10:ℝ)*L)=Real.exp L := by
      rw [←Real.exp_add]
      congr 1
      ring
    calc
      _ = (1/100:ℝ)*(Real.exp ((1/10:ℝ)*L)*Real.exp ((9/10:ℝ)*L)) := by ring
      _ = _ := by rw [heq]
  rw [hexprod] at hprod
  have hnum : (2*supplyTruncation L:ℕ)*(1+2*Real.exp ((9/10:ℝ)*L)) ≤
      (1/100:ℝ)*Real.exp L := by
    have hk0 : (0:ℝ)≤(2*supplyTruncation L:ℕ) := Nat.cast_nonneg _
    nlinarith
  apply hwp.trans
  calc
    _ ≤ Real.exp ((1/100:ℝ)*Real.exp L) := Real.exp_le_exp.mpr hnum
    _ ≤ Real.exp (Real.log ((((supplyRadius L)^2:ℕ):ℝ))*(1/100:ℝ)) :=
      Real.exp_le_exp.mpr (by nlinarith [exp_le_supply_square_log L])
    _ = _ := (Real.rpow_def_of_pos (by exact_mod_cast pow_pos (supplyRadius_pos L) 2) _).symm

theorem eventually_boundary_inverse_main_bound (E : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      ((((supplyRadius L)^2:ℕ):ℝ))^(-(1/100:ℝ)) ≤ Real.exp (-E*L) := by
  have hc : 0 < 1/(100*(|E|+1)) := by positivity
  have hb := (isLittleO_pow_exp_pos_mul_atTop 1 (by norm_num : (0:ℝ)<1)).bound hc
  filter_upwards [hb,eventually_ge_atTop (0:ℝ)] with L hb hL
  simp only [pow_one,one_mul,Real.norm_eq_abs,abs_of_nonneg hL,
    abs_of_pos (Real.exp_pos _)] at hb
  have hmul := mul_le_mul_of_nonneg_left hb (show 0≤|E|+1 by positivity)
  have he : E*L ≤ (1/100:ℝ)*Real.exp L := by
    have hE := le_abs_self E
    have hid : (|E|+1)*(1/(100*(|E|+1))) = (1/100:ℝ) := by
      field_simp
    rw [←mul_assoc,hid] at hmul
    nlinarith
  rw [Real.rpow_def_of_pos (by exact_mod_cast pow_pos (supplyRadius_pos L) 2)]
  apply Real.exp_le_exp.mpr
  nlinarith [exp_le_supply_square_log L]

end Ostmann.Supply

end

end OAI
