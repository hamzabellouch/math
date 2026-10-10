import OAI.NumberTheory.Ostmann.Characters.InitialCharacterStatisticLower
import OAI.NumberTheory.Ostmann.Characters.InitialCharacterStatisticScaleAbsorption

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators FourierTransform
namespace Ostmann.Characters.InitialCharacterScale
open Construction Preliminaries Filter

lemma sqrt_ratio_le_gap {X M Δ D : ℝ} (hX : 0 < X)
    (hM : X*Real.exp (Δ-D) ≤ M) :
    Real.sqrt X/Real.sqrt M ≤ Real.exp (-(Δ-D)/2) := by
  have hexp : Real.sqrt (Real.exp (Δ-D)) = Real.exp ((Δ-D)/2) := by
    apply (Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos _).le (Real.exp_pos _).le).mpr
    rw [← Real.exp_add]
    congr 1
    ring
  have hs := Real.sqrt_le_sqrt hM
  rw [Real.sqrt_mul hX.le, hexp] at hs
  calc
    _ ≤ Real.sqrt X/(Real.sqrt X*Real.exp ((Δ-D)/2)) :=
      div_le_div_of_nonneg_left (Real.sqrt_nonneg _)
        (mul_pos (Real.sqrt_pos.mpr hX) (Real.exp_pos _)) hs
    _ = 1/Real.exp ((Δ-D)/2) := by
      field_simp
    _ = _ := by rw [one_div, ← Real.exp_neg]; congr 1; ring

def sourceErrorConstant (c₀ C D DH : ℝ) : ℝ :=
  ‖𝓕 SchwartzCutoff.psi 0‖/c₀^2*Real.exp (D/2)*Real.exp (2*C)*Real.exp DH

theorem source_error_bound {Q b : ℕ} (E : Fin b → Finset (PrimeUpTo Q))
    (hE : ∀ i, 0 < primeShellMass (E i))
    {ρ c₀ C N L X M₀ BD D H DH : ℝ} (hρ : 0 < ρ) (hc₀ : 0 < c₀)
    (hC : 0 ≤ C) (hL : 0 < L) (hX : 0 < X) (k : ℕ) (hNz : N ≤ depthScale k)
    (hNorm : (∏ i, (primeShellMass (E i))⁻¹) ≤
      (1/(ρ*L))^(wordSize k L)/c₀*Real.exp (C*N*L))
    (hUnion : primeShellMass (Finset.univ.biUnion E) ≤ H*L+DH)
    (hM : X*Real.exp (initialGap BD k L-D) ≤ M₀) :
    initialCharacterRepeatedError E X M₀ ≤
      sourceErrorConstant c₀ C D DH*Real.exp (-initialGap BD k L/2)*
        (1/(ρ*L))^(2*wordSize k L)*Real.exp ((2*C)*(wordSize k L : ℝ))*
        (((b+b : ℕ) : ℝ)^(b+b))*Real.exp (H*L) := by
  let m := wordSize k L
  have hNL : N*L ≤ (m : ℝ)+1 := by
    have hh := mul_le_mul_of_nonneg_right hNz hL.le
    have hf := (wordSize_bounds k hL.le).1
    change depthScale k*L-1 < (m : ℝ) at hf
    linarith
  have hNorm' : (∏ i, (primeShellMass (E i))⁻¹) ≤
      (1/(ρ*L))^m/c₀*Real.exp C*Real.exp (C*(m : ℝ)) := by
    apply hNorm.trans
    have he : Real.exp (C*N*L) ≤ Real.exp C*Real.exp (C*(m : ℝ)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hNL hC]
    exact (mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ (1/(ρ*L))^m/c₀)).trans_eq
      (mul_assoc _ _ _).symm
  have hN0 : 0 ≤ ∏ i, (primeShellMass (E i))⁻¹ :=
    Finset.prod_nonneg (fun i _ => inv_nonneg.mpr (hE i).le)
  have hratio := sqrt_ratio_le_gap hX hM
  have hUnion' := Real.exp_le_exp.mpr hUnion
  have hsplit : Real.exp (-(initialGap BD k L-D)/2) =
      Real.exp (D/2)*Real.exp (-initialGap BD k L/2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hpowC : (Real.exp C)^2 = Real.exp (2*C) := by rw [← Real.exp_nat_mul]; norm_num
  have hpowCm : (Real.exp (C*(m : ℝ)))^2 = Real.exp ((2*C)*(m : ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  calc
    _ = ‖𝓕 SchwartzCutoff.psi 0‖*(Real.sqrt X/Real.sqrt M₀)*
        (∏ i, (primeShellMass (E i))⁻¹)^2 *
        (((b+b : ℕ) : ℝ)^(b+b))*Real.exp (primeShellMass (Finset.univ.biUnion E)) := by
      unfold initialCharacterRepeatedError
      ring
    _ ≤ ‖𝓕 SchwartzCutoff.psi 0‖*Real.exp (-(initialGap BD k L-D)/2)*
        ((1/(ρ*L))^m/c₀*Real.exp C*Real.exp (C*(m : ℝ)))^2 *
        (((b+b : ℕ) : ℝ)^(b+b))*Real.exp (H*L+DH) := by
      gcongr
    _ = _ := by
      rw [hsplit, mul_pow, mul_pow, div_pow, ← pow_mul, hpowC, hpowCm, Real.exp_add]
      dsimp only [sourceErrorConstant]
      rw [Nat.mul_comm m 2]
      ring

end Ostmann.Characters.InitialCharacterScale

end

end OAI
