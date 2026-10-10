import OAI.NumberTheory.Ostmann.Characters.OneSidedScaleGapSum
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationCompiled
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedNumericInputsAtoms
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhasePriorJoinBoundedRows

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators SchwartzMap
namespace Ostmann.Characters.TemplateOneSidedCancellation
open Construction Preliminaries PrimeDyadicCover TemplateOneSidedPrior
open Template.OneSidedPhase

def primePriorConstant (C z c β : ℝ) : ℝ :=
  C+(c+β)/z+|Real.log (1/Real.log 2+1)|+1

theorem primePriorConstant_pos {C z c β : ℝ} (hC : 0 ≤ C) (hz : 0 < z)
    (hc : 0 ≤ c) (hβ : 0 ≤ β) : 0 < primePriorConstant C z c β := by
  unfold primePriorConstant
  positivity

theorem primePriorCost_bounds (C z c β L : ℝ) (d : ℕ)
    (hC : 0 ≤ C) (hz : 0 < z) (hc : 0 ≤ c) (hβ : 0 ≤ β) (hL : 0 ≤ L) :
    historyPolynomialCost C z d L ≤ historyPolynomialCost (primePriorConstant C z c β) z (d+1) L ∧
    c*L ≤ historyPolynomialCost (primePriorConstant C z c β) z (d+1) L ∧
    Real.log (1/Real.log 2+1)+β*L ≤
      historyPolynomialCost (primePriorConstant C z c β) z (d+1) L := by
  let M : ℝ := 1+(⌊z*L⌋₊:ℝ)
  have hM : 1 ≤ M := by dsimp [M]; linarith [Nat.cast_nonneg (α:=ℝ) ⌊z*L⌋₊]
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hLM : z*L ≤ M := by
    simpa only [M,add_comm] using (Nat.lt_floor_add_one (z*L)).le
  have hpow : M^d ≤ M^(d+1) := pow_le_pow_right₀ hM (by omega)
  have hMp : M ≤ M^(d+1) := by
    simpa only [pow_one] using pow_le_pow_right₀ hM (show 1 ≤ d+1 by omega)
  have hp1 : 1 ≤ M^(d+1) := one_le_pow₀ hM
  have hdiv : 0 ≤ (c+β)/z := by positivity
  have hlinear : (c+β)*L ≤ ((c+β)/z)*M := by
    calc
      _ = ((c+β)/z)*(z*L) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hLM hdiv
  have hlin' : (c+β)*L ≤ ((c+β)/z)*M^(d+1) :=
    hlinear.trans (mul_le_mul_of_nonneg_left hMp hdiv)
  have hlog : |Real.log (1/Real.log 2+1)| ≤
      |Real.log (1/Real.log 2+1)| *M^(d+1) :=
    le_mul_of_one_le_right (abs_nonneg _) hp1
  have hcP : 0 ≤ C*M^(d+1) := mul_nonneg hC (pow_nonneg hM0 _)
  have hCp : C*M^d ≤ C*M^(d+1) := mul_le_mul_of_nonneg_left hpow hC
  have hdivP : 0 ≤ ((c+β)/z)*M^(d+1) := mul_nonneg hdiv (pow_nonneg hM0 _)
  have hlogP : 0 ≤ |Real.log (1/Real.log 2+1)| *M^(d+1) := by positivity
  change C*M^d ≤ (C+(c+β)/z+|Real.log (1/Real.log 2+1)|+1)*M^(d+1) ∧
    c*L ≤ (C+(c+β)/z+|Real.log (1/Real.log 2+1)|+1)*M^(d+1) ∧
    Real.log (1/Real.log 2+1)+β*L ≤
      (C+(c+β)/z+|Real.log (1/Real.log 2+1)|+1)*M^(d+1)
  constructor
  · nlinarith
  constructor
  · nlinarith [mul_nonneg hβ hL]
  · nlinarith [le_abs_self (Real.log (1/Real.log 2+1)),mul_nonneg hc hL]

theorem sourceShortMass_max_le {A : ℕ} (E : Finset (PrimeUpTo A))
    (hE : 0 < primeShellMass E) {b : ℝ} (hb : 0 ≤ b)
    (h : ∀p,(primeShellPrior E hE).mass p ≤ b) :
    priorMaxAtom (sourceShortMass E hE) ≤ b := by
  change ((Finset.univ.sup (fun q : ↥E => (sourceShortMass E hE q).toNNReal) : NNReal):ℝ) ≤ b
  have hs : Finset.univ.sup (fun q : ↥E => (sourceShortMass E hE q).toNNReal) ≤ b.toNNReal := by
    apply Finset.sup_le
    intro q hq
    exact Real.toNNReal_le_toNNReal (h q.val)
  exact (by exact_mod_cast hs : ((Finset.univ.sup
    (fun q : ↥E => (sourceShortMass E hE q).toNNReal) : NNReal):ℝ) ≤ (b.toNNReal:ℝ)).trans
    (by rw [Real.coe_toNNReal _ hb])

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
