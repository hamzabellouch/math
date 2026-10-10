import OAI.NumberTheory.Ostmann.QuadraticCenter.ParameterAuxiliaryBand

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Ostmann.Characters Ostmann.Preliminaries Filter
open scoped BigOperators

def boundedClosedLogarithmicPrimeBand (Q : ℕ) (T : ℝ) : Finset (PrimeUpTo Q) := by
  classical
  exact Finset.univ.filter (fun p => T ≤ Real.log p.val ∧ Real.log p.val ≤ 2*T)

@[simp] lemma mem_boundedClosedLogarithmicPrimeBand {Q : ℕ} {T : ℝ} {p : PrimeUpTo Q} :
    p ∈ boundedClosedLogarithmicPrimeBand Q T ↔ T ≤ Real.log p.val ∧ Real.log p.val ≤ 2*T := by
  classical
  simp [boundedClosedLogarithmicPrimeBand]

def quadraticBadBandMass (d : Decomposition) (δ T : ℝ) : ℝ :=
  boundedPrimeWeight (quadraticBiasedPrimes d (collisionScale 4 (parameterX T)) δ
    (boundedClosedLogarithmicPrimeBand (collisionScale 4 (parameterX T)) T))

lemma quadraticBadBandMass_nonneg (d : Decomposition) (δ T : ℝ) :
    0 ≤ quadraticBadBandMass d δ T := by
  unfold quadraticBadBandMass boundedPrimeWeight
  exact Finset.sum_nonneg (fun p hp => bounded_prime_weight_nonneg p)

theorem eventually_biasSelectionCost_le (δ : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᶠ T : ℝ in atTop,
      biasSelectionCost δ*Real.log (Real.log (parameterX T : ℝ)) ≤ ρ*T/2 := by
  have hc := collisionConstant_pos 4
  have hC : 0 ≤ biasSelectionCost δ := by unfold biasSelectionCost; positivity
  have hl := ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).const_mul_left
    (biasSelectionCost δ*(8/5))).bound (by positivity : 0 < ρ/2)
  filter_upwards [eventually_parameterX_log_bounds,hl] with T hT hlog
  have ht : 0 ≤ T := by linarith [hT.1]
  simp only [Real.rpow_one,Real.norm_eq_abs,abs_of_nonneg ht] at hlog
  have hh := mul_le_mul_of_nonneg_left hT.2.2.2.2 hC
  calc
    _ ≤ biasSelectionCost δ*((8/5)*Real.log T) := hh
    _ ≤ |(biasSelectionCost δ*(8/5))*Real.log T| := by
      rw [mul_assoc]
      exact le_abs_self _
    _ ≤ ρ*T/2 := by nlinarith

end Ostmann.QuadraticCenter

end

end OAI
