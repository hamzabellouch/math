import OAI.NumberTheory.Ostmann.ZeroDensity.SupplyContourScales
import OAI.NumberTheory.Ostmann.ZeroDensity.SupplyZeroDecay

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators Topology
open Filter
namespace Ostmann.ZeroDensity

theorem eventually_literal_supply_zero_decay (P : ℕ) {E : ℝ} (hE : 0 ≤ E) (D : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ exception : Option (PrimitiveFamily (supplyConductorCutoff L)),
      (∑ z ∈ retainedZeros (supplyConductorCutoff L) exception (1/2)
          (supplyContourHeight P E L : ℝ), (supplyPrimeSample L : ℝ)^z.point.re) ≤
        (supplyPrimeSample L : ℝ)*Real.exp (-D*L) := by
  have hbudget : 0 < 20003*((P : ℝ)+1)+E+8 := by positivity
  have hd := eventually_zero_power_supply_decay hbudget D
  filter_upwards [hd,eventually_ge_atTop (1 : ℝ)] with L hd hL
  intro exception
  have hX : (1 : ℝ) < supplyPrimeSample L := by
    by_contra! hh
    have hlog := Real.log_nonpos (Nat.cast_nonneg (supplyPrimeSample L)) hh
    have hlo := log_supplyPrimeSample_lower L
    have hp := Real.exp_pos L
    linarith
  have hH : 0 < supplyContourHeight P E L := by
    have hh := supplyContourHeight_ge_two P E L
    omega
  have hlog := log_supplyPrimeSample_bounds hL
  exact hd (supplyConductorCutoff L) (supplyContourHeight P E L) exception
    (supplyPrimeSample L : ℝ) (supplyConductorCutoff_pos L) hH hX hlog.1 hlog.2
    (supplyContourHeight_modulus_budget P hE hL)

theorem eventually_literal_supply_zero_decay_succ (P : ℕ) {E : ℝ} (hE : 0 ≤ E) (D : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ exception : Option (PrimitiveFamily (supplyConductorCutoff L)),
      (∑ z ∈ retainedZeros (supplyConductorCutoff L) exception (1/2)
          ((supplyContourHeight P E L+1 : ℕ) : ℝ), (supplyPrimeSample L : ℝ)^z.point.re) ≤
        (supplyPrimeSample L : ℝ)*Real.exp (-D*L) := by
  have hbudget : 0 < 20003*((P : ℝ)+1)+E+9 := by positivity
  have hd := eventually_zero_power_supply_decay hbudget D
  filter_upwards [hd,eventually_ge_atTop (1 : ℝ)] with L hd hL
  intro exception
  have hX : (1 : ℝ) < supplyPrimeSample L := by
    by_contra! hh
    have hlog := Real.log_nonpos (Nat.cast_nonneg (supplyPrimeSample L)) hh
    have hlo := log_supplyPrimeSample_lower L
    have hp := Real.exp_pos L
    linarith
  have hlog := log_supplyPrimeSample_bounds hL
  exact hd (supplyConductorCutoff L) (supplyContourHeight P E L+1) exception
    (supplyPrimeSample L : ℝ) (supplyConductorCutoff_pos L) (by omega) hX hlog.1 hlog.2
    (supplyContourHeight_succ_modulus_budget P hE hL)

theorem eventually_uniform_supply_zero_decay_succ (P : ℕ) {E : ℝ} (hE : 0 ≤ E) (D : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ Q : ℕ, 0 < Q → Q ≤ supplyConductorCutoff L →
      ∀ exception : Option (PrimitiveFamily Q),
      (∑ z ∈ retainedZeros Q exception (1/2)
          ((supplyContourHeight P E L+1 : ℕ) : ℝ), (supplyPrimeSample L : ℝ)^z.point.re) ≤
        (supplyPrimeSample L : ℝ)*Real.exp (-D*L) := by
  have hbudget : 0 < 20003*((P : ℝ)+1)+E+9 := by positivity
  have hd := eventually_zero_power_supply_decay hbudget D
  filter_upwards [hd,eventually_ge_atTop (1 : ℝ)] with L hd hL
  intro Q hQ hQQ exception
  let : NeZero Q := ⟨by omega⟩
  let : NeZero (supplyConductorCutoff L) := ⟨Nat.ne_of_gt (supplyConductorCutoff_pos L)⟩
  have hX : (1 : ℝ) < supplyPrimeSample L := by
    by_contra! hh
    have hlog := Real.log_nonpos (Nat.cast_nonneg (supplyPrimeSample L)) hh
    have hlo := log_supplyPrimeSample_lower L
    have hp := Real.exp_pos L
    linarith
  have hlog := log_supplyPrimeSample_bounds hL
  apply hd Q (supplyContourHeight P E L+1) exception
    (supplyPrimeSample L : ℝ) hQ (by omega) hX hlog.1 hlog.2
  exact (Erdos970.Erdos970Dependency.SiegelWalfisz.modulusHeight_mono hQQ _).trans
    (supplyContourHeight_succ_modulus_budget P hE hL)

end Ostmann.ZeroDensity

end

end OAI
