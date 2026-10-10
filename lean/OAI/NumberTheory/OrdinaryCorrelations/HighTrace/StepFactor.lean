import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.KappaPos

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.FiniteIntegration
open Finset Classical
variable {S : PrimeSystem} {h ℓ : ℕ}

def stepFactor (S : PrimeSystem) (w : ClosedLine h ℓ) (p : S.Index)
    (i : Fin ℓ) (a : ZMod (p : ℕ)) : ℝ :=
  S.occurrenceFactor w p i a * S.beta p ^
    (if a + (w.offset i.castSucc : ZMod (p : ℕ)) = 0 then (1 : ℕ) else 0)

def primeCharge (S : PrimeSystem) (p : S.Index) (d : ℕ) (b : ℤ)
    (a : ZMod (p : ℕ)) : ℝ :=
  if S.IsCore p ∧ ¬(p : ℕ) ∣ d ∧ a + (b : ZMod (p : ℕ)) = 0 then
    Real.exp kappa else 1

lemma primeCharge_nonneg (p : S.Index) (d : ℕ) (b : ℤ) (a : ZMod (p : ℕ)) :
    0 ≤ S.primeCharge p d b a := by unfold primeCharge; split_ifs <;> positivity

lemma theta_div_bounds (p : S.Index) : 0 ≤ theta / (p : ℝ) ∧ theta / (p : ℝ) ≤ 1 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast NeZero.pos (p : ℕ)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast NeZero.pos (p : ℕ)
  constructor
  · exact div_nonneg (by norm_num) hp.le
  · apply (div_le_iff₀ hp).mpr
    simpa using (show theta ≤ (1 : ℝ) by norm_num).trans hp1

lemma beta_eq_core (p : S.Index) (hc : S.IsCore p) : S.beta p = betaC := by
  simp only [beta, amplitude, hc, ite_true, betaC]

lemma beta_eq_center (p : S.Index) (hc : ¬S.IsCore p) : S.beta p = betaZ := by
  simp only [beta, amplitude, hc, ite_false, betaZ]

theorem charged_return_le_one (w : ClosedLine h ℓ) (p : S.Index)
    (i : Fin ℓ) (a : ZMod (p : ℕ)) :
    |S.stepFactor w p i a| * S.primeCharge p (w.label i) (w.offset i.castSucc) a ≤ 1 := by
  have ht := theta_div_bounds p
  have hb0 : (0 : ℝ) ≤ betaZ := by norm_num
  have hb1 : betaZ ≤ 1 := by norm_num
  by_cases hc : S.IsCore p
  · rw [stepFactor, beta_eq_core p hc]
    by_cases hd : (p : ℕ) ∣ w.label i <;>
      by_cases ha : a + (w.offset i.castSucc : ZMod (p : ℕ)) = 0
    · simpa only [occurrenceFactor, hc, hd, ha, ite_true, activity,
        pow_one, mul_one, primeCharge, not_true_eq_false, false_and, and_false, ite_false,
        abs_of_nonneg (mul_nonneg A_pos.le betaC_pos.le)] using A_mul_betaC_le_one
    · simp [occurrenceFactor, hc, hd, ha, activity, primeCharge]
    · simpa only [occurrenceFactor, hc, hd, ha, ite_false, ite_true, pow_one, one_mul,
        primeCharge, not_false_eq_true, and_self, abs_of_pos betaC_pos] using betaC_mul_exp_le_one
    · simp [occurrenceFactor, hc, hd, ha, primeCharge]
  · rw [stepFactor, beta_eq_center p hc]
    by_cases hd : (p : ℕ) ∣ w.label i <;>
      by_cases ha : a + (w.offset i.castSucc : ZMod (p : ℕ)) = 0
    · simp only [occurrenceFactor, hc, hd, ha, ite_true, ite_false, activity,
        pow_one, primeCharge, false_and, mul_one]
      rw [abs_of_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) hb0)]
      exact (mul_le_mul_of_nonneg_right (by linarith : 1 - theta / (p : ℝ) ≤ 1) hb0).trans
        (by simpa using hb1)
    · simp only [occurrenceFactor, hc, hd, ha, ite_true, ite_false, activity,
        pow_zero, primeCharge, false_and, mul_one, zero_sub, abs_neg,
        abs_of_nonneg ht.1]
      exact ht.2
    · simp only [occurrenceFactor, hd, ha, ite_false, ite_true, pow_one,
        primeCharge, hc, false_and, one_mul, mul_one, abs_of_nonneg hb0]
      exact hb1
    · simp [occurrenceFactor, hd, ha, primeCharge, hc]

lemma primeFactor_split_steps (w : ClosedLine h ℓ) (p : S.Index) (a : ZMod (p : ℕ)) :
    S.primeFactor w p a =
      (∏ i ∈ w.treeSteps, S.stepFactor w p i a) *
      ∏ i ∈ univ \ w.treeSteps, S.stepFactor w p i a := by
  change (∏ i ∈ univ, S.stepFactor w p i a) = _
  rw [← prod_union disjoint_sdiff_self_right, union_sdiff_of_subset (subset_univ _)]

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
