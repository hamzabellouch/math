import OAI.NumberTheory.Ostmann.Characters.PrimeDyadicCover

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.PrimeDyadicCover
open Preliminaries

def costConstant : ℝ := 3*(1/Real.log 2+1)

theorem costConstant_pos : 0 < costConstant := by
  have h : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold costConstant
  positivity

theorem shell_cost_le {N U : ℕ} (E : Finset (PrimeUpTo N)) (hE : 0 < primeShellMass E)
    {β c L : ℝ} (hβ : 0 ≤ β) (hL : 0 ≤ L)
    (hN : Real.log U ≤ Real.exp (β*L)) (hZ : Real.exp (-c*L) ≤ primeShellMass E) :
    (shellResidueCost (J:=Index U) E hE:ℝ) ≤ costConstant*Real.exp ((β+c)*L) := by
  have hinv : 1/primeShellMass E ≤ Real.exp (c*L) := by
    have h := one_div_le_one_div_of_le (Real.exp_pos (-c*L)) hZ
    simpa only [one_div,← Real.exp_neg,neg_mul,neg_neg] using h
  have hcard := card_le_exp hβ hL hN
  change 3*(Fintype.card (Index U):ℝ)/primeShellMass E ≤ _
  calc
    _ = (3*(Fintype.card (Index U):ℝ))*(1/primeShellMass E) := by ring
    _ ≤ (3*((1/Real.log 2+1)*Real.exp (β*L)))*Real.exp (c*L) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hcard (by norm_num)) hinv
        (by positivity) (by have h := costConstant_pos; dsimp [costConstant] at h; positivity)
    _ = _ := by simp only [add_mul,Real.exp_add,costConstant]; ring

theorem shell_cost_le_exp {N U : ℕ} (E : Finset (PrimeUpTo N)) (hE : 0 < primeShellMass E)
    {β c L : ℝ} (hβ : 0 ≤ β) (hL : 0 ≤ L)
    (hN : Real.log U ≤ Real.exp (β*L)) (hZ : Real.exp (-c*L) ≤ primeShellMass E)
    (hlarge : Real.log costConstant ≤ L) :
    (shellResidueCost (J:=Index U) E hE:ℝ) ≤ Real.exp ((β+c+1)*L) := by
  have hc : costConstant ≤ Real.exp L := by
    have hh := Real.exp_le_exp.mpr hlarge
    simpa only [Real.exp_log costConstant_pos] using hh
  calc
    _ ≤ costConstant*Real.exp ((β+c)*L) := shell_cost_le E hE hβ hL hN hZ
    _ ≤ Real.exp L*Real.exp ((β+c)*L) :=
      mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem prime_cost_le_exp {N U Q : ℕ} [NeZero Q]
    (E : Finset (PrimeUpTo N)) (hE : 0 < primeShellMass E)
    {β c L : ℝ} (hβ : 0 ≤ β) (hL : 0 ≤ L)
    (hN : Real.log U ≤ Real.exp (β*L)) (hZ : Real.exp (-c*L) ≤ primeShellMass E)
    (hlarge : Real.log costConstant ≤ L) :
    (primeResidueCost (Q:=Q) (J:=Index U) E hE:ℝ) ≤ Real.exp ((β+c+1)*L) :=
  (show (primeResidueCost (Q:=Q) (J:=Index U) E hE:ℝ) ≤
    (shellResidueCost (J:=Index U) E hE:ℝ) from primeResidueCost_le_shell E hE).trans
      (shell_cost_le_exp E hE hβ hL hN hZ hlarge)

theorem binary_cost_le_exp (D : List Bool → NNReal) (T : ℝ)
    (hD : ∀ p, (D p:ℝ) ≤ Real.exp T) (j : ℕ) (p : List Bool) :
    (BinaryPriorExposure.cost D j p:ℝ) ≤ Real.exp ((2:ℝ)^j*T) := by
  induction j generalizing p with
  | zero => simpa only [BinaryPriorExposure.cost,pow_zero,one_mul] using hD p
  | succ j ih =>
    change (BinaryPriorExposure.cost D j (false::p):ℝ)*
      (BinaryPriorExposure.cost D j (true::p):ℝ) ≤ _
    calc
      _ ≤ Real.exp ((2:ℝ)^j*T)*Real.exp ((2:ℝ)^j*T) :=
        mul_le_mul (ih _) (ih _) (NNReal.coe_nonneg _) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add,pow_succ]; congr 1; ring

theorem prime_binary_cost_le_exp {N U Q : ℕ} [NeZero Q]
    (E : List Bool → Finset (PrimeUpTo N)) (hE : ∀ p, 0 < primeShellMass (E p))
    {β c L : ℝ} (hβ : 0 ≤ β) (hL : 0 ≤ L)
    (hN : Real.log U ≤ Real.exp (β*L))
    (hZ : ∀ p, Real.exp (-c*L) ≤ primeShellMass (E p))
    (hlarge : Real.log costConstant ≤ L) (j : ℕ) (p : List Bool) :
    (BinaryPriorExposure.cost
      (fun p => primeResidueCost (Q:=Q) (J:=Index U) (E p) (hE p)) j p:ℝ) ≤
      Real.exp ((β+c+1)*(2:ℝ)^j*L) := by
  have hh := binary_cost_le_exp
    (fun p => primeResidueCost (Q:=Q) (J:=Index U) (E p) (hE p)) ((β+c+1)*L)
    (fun p => prime_cost_le_exp (E p) (hE p) hβ hL hN (hZ p) hlarge) j p
  convert hh using 1; congr 1; ring

end Ostmann.Characters.PrimeDyadicCover

end

end OAI
