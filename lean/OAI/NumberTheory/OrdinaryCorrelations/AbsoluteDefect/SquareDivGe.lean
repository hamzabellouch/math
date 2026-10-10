import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter

namespace OrdinaryDivisionHeight

lemma square_div_ge {X K : ℕ} (hK : 0<K) (hX : 4*K^2≤X) : X≤(X/K)^2 := by
  have hh : 2*K≤X/K := (Nat.le_div_iff_mul_le hK).mpr (by nlinarith)
  have hy := Nat.lt_mul_div_succ X hK
  have hq : 1≤X/K := by omega
  nlinarith

lemma div_height {X K D : ℕ} (hK : 0<K) (hX : K≤X) (hD : 2*K≤D) :
    (X:ℝ)/(D:ℝ)≤(X/K:ℕ) := by
  have hDp : 0<(D:ℝ) := by exact_mod_cast (show 0<D by omega)
  apply (div_le_iff₀ hDp).mpr
  have hq : 1≤X/K := Nat.div_pos hX hK
  have hh := Nat.lt_mul_div_succ X hK
  have hmul : X≤(X/K)*D := by nlinarith
  exact_mod_cast hmul

lemma power_card_div {c X K r : ℕ} (hK : 0<K) (hX : 4*K^2≤X)
    (hc : c^(2*r)≤X) : c^r≤X/K := by
  have hh := hc.trans (square_div_ge hK hX)
  rw [show 2*r=r*2 by omega,pow_mul] at hh
  exact (Nat.pow_le_pow_iff_left (by norm_num : 2 ≠ 0)).mp hh

end OrdinaryDivisionHeight

end

end OAI
