import OAI.NumberTheory.Ostmann.ZeroDensity.HeightBudgets
import OAI.NumberTheory.Ostmann.ZeroDensity.WeightedPowers

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators Topology
open Filter
namespace Ostmann.ZeroDensity

theorem eventually_zero_power_supply_decay {B : ℝ} (hB : 0 < B) (D : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (Q H : ℕ) (exception : Option (PrimitiveFamily Q)) (X : ℝ),
      0 < Q → 0 < H → 1 < X → Real.exp L ≤ Real.log X → Real.log X ≤ 2*Real.exp L →
      Erdos970.Erdos970Dependency.SiegelWalfisz.modulusHeight Q (H : ℝ) ≤ B*L*Real.exp (9*L/10) →
      (∑ z ∈ retainedZeros Q exception (1/2) (H : ℝ), X^z.point.re) ≤
        X*Real.exp (-D*L) := by
  obtain ⟨c,C,hc,hC,hpower⟩ := exists_unconditional_zero_power_constants
  have hfirst := eventually_linear_mul_exp_le (a := (9 : ℝ)/10) (b := 1)
    (by norm_num) (40*B)
  have hsecond := eventually_linear_mul_exp_le (a := (9 : ℝ)/10) (b := 2)
    (by norm_num) (B+1)
  have hdecay := eventually_supply_prefactor_decay
    (c := c/(2*B)) (by positivity) 23 D
  filter_upwards [hfirst,hsecond,hdecay,eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop (Real.log C)] with L hfirst hsecond hdecay hL hLC
  intro Q H exception X hQ hH hX hMX hXM hbudget
  let : NeZero Q := ⟨by omega⟩
  have hLp : 0 < L := by linarith
  have hM : 0 < Real.log X := Real.log_pos hX
  have hHgt := Erdos970.Erdos970Dependency.SiegelWalfisz.modulusHeight_ge_one Q (H : ℝ)
  have hHpos : 0 < Erdos970.Erdos970Dependency.SiegelWalfisz.modulusHeight Q (H : ℝ) := by linarith
  have hExp : 1 ≤ Real.exp (9*L/10) := Real.one_le_exp (by positivity)
  have hLog0 : 0 ≤ 1+Real.log (Q*H : ℕ) := by
    have hn : (1 : ℝ) ≤ (Q*H : ℕ) := by exact_mod_cast Nat.mul_pos hQ hH
    have hh := Real.log_nonneg hn
    linarith
  have hLog : 1+Real.log (Q*H : ℕ) ≤ Real.exp (2*L) := by
    have hh := conductor_height_log_le Q H hQ hH
    have hm : 1+Real.log (Q*H : ℕ) ≤ (B+1)*L*Real.exp (9*L/10) := by
      nlinarith
    have he : (9 : ℝ)/10*L = 9*L/10 := by ring
    rw [he] at hsecond
    exact hm.trans hsecond
  have hscale : 2*(10*Real.log ((Q^2*H : ℕ) : ℝ)) ≤ Real.log X := by
    have hh := density_height_log_le Q H hQ hH
    have he : (9 : ℝ)/10*L = 9*L/10 := by ring
    rw [he,one_mul] at hfirst
    nlinarith
  have hsum := hpower Q H exception X hQ hH hX hscale
  have hfloor : (⌊Real.log X/2⌋₊+1 : ℝ) ≤ Real.exp L+1 := by
    have hf := Nat.floor_le (show 0 ≤ Real.log X/2 by positivity)
    linarith
  have hCexp : C ≤ Real.exp L := by
    calc
      C = Real.exp (Real.log C) := (Real.exp_log hC).symm
      _ ≤ _ := Real.exp_le_exp.mpr hLC
  have hloss : C*(1+Real.log (Q*H : ℕ))^11 ≤ Real.exp (23*L) := by
    calc
      _ ≤ Real.exp L*(Real.exp (2*L))^11 := by
        exact mul_le_mul hCexp (pow_le_pow_left₀ hLog0 hLog 11)
          (pow_nonneg hLog0 11) (Real.exp_pos L).le
      _ = _ := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        ring
  have hgap := density_height_gap_gain hc hB hLp hHpos hMX hbudget
  have hgain : Real.exp (1-Real.log X*(c/Erdos970.Erdos970Dependency.SiegelWalfisz.modulusHeight Q (H : ℝ))/2) ≤
      Real.exp (1-(c/(2*B))*Real.exp (L/10)/L) := by
    exact Real.exp_le_exp.mpr (by linarith)
  calc
    _ ≤ X*(⌊Real.log X/2⌋₊+1 : ℝ)*(C*(1+Real.log (Q*H : ℕ))^11)*
        Real.exp (1-Real.log X*(c/Erdos970.Erdos970Dependency.SiegelWalfisz.modulusHeight Q (H : ℝ))/2) := hsum
    _ ≤ X*(Real.exp L+1)*Real.exp (23*L)*
        Real.exp (1-(c/(2*B))*Real.exp (L/10)/L) := by
      gcongr
    _ = X*((Real.exp L+1)*Real.exp (23*L)*
        Real.exp (1-(c/(2*B))*Real.exp (L/10)/L)) := by ring
    _ ≤ X*Real.exp (-D*L) := mul_le_mul_of_nonneg_left hdecay (by linarith)

end Ostmann.ZeroDensity

end

end OAI
