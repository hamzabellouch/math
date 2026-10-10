import OAI.Probability.MatroidProphet.Information
import OAI.Probability.MatroidProphet.FiniteBits
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Basic.ENNReal.BigOperators

namespace OAI

namespace MatroidProphet

open MeasureTheory Finset

noncomputable def seedSet {bits : ℕ} (r : Seed bits) : Finset (Fin bits) :=
  Finset.univ.filter fun e => r e = true

noncomputable def setSeed {bits : ℕ} (S : Finset (Fin bits)) : Seed bits :=
  fun e => decide (e ∈ S)

@[simp] lemma seedSet_setSeed {bits : ℕ} (S : Finset (Fin bits)) : seedSet (setSeed S) = S := by
  classical
  ext e
  simp [seedSet, setSeed]

@[simp] lemma setSeed_seedSet {bits : ℕ} (r : Seed bits) : setSeed (seedSet r) = r := by
  funext e
  simp [seedSet, setSeed]

noncomputable def seedFinsetEquiv (bits : ℕ) : Seed bits ≃ Finset (Fin bits) where
  toFun := seedSet
  invFun := setSeed
  left_inv := setSeed_seedSet
  right_inv := seedSet_setSeed

lemma seedWeight_sum {bits : ℕ} (q : Fin bits → ℝ) :
    (∑ r : Seed bits, bitsWeight q Finset.univ (seedSet r)) = 1 := by
  classical
  have h := (seedFinsetEquiv bits).sum_comp (bitsWeight q Finset.univ)
  change (∑ r, bitsWeight q Finset.univ ((seedFinsetEquiv bits) r)) = 1
  rw [h]
  simpa only [bitsExpectation, Finset.powerset_univ, mul_one] using
    bitsExpectation_one q Finset.univ

noncomputable def seedPMF {bits : ℕ} (q : Fin bits → ℝ)
    (h0 : ∀ e, 0 ≤ q e) (h1 : ∀ e, q e ≤ 1) : PMF (Seed bits) :=
  PMF.ofFintype (fun r => ENNReal.ofReal (bitsWeight q Finset.univ (seedSet r))) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun r _ => bitsWeight_nonneg q h0 h1 _ _),
      seedWeight_sum, ENNReal.ofReal_one])

noncomputable def bernoulliSeedLaw {bits : ℕ} (q : Fin bits → ℝ)
    (h0 : ∀ e, 0 ≤ q e) (h1 : ∀ e, q e ≤ 1) : Measure (Seed bits) :=
  (seedPMF q h0 h1).toMeasure

instance bernoulliSeedLaw_probability {bits : ℕ} (q : Fin bits → ℝ)
    (h0 : ∀ e, 0 ≤ q e) (h1 : ∀ e, q e ≤ 1) :
    IsProbabilityMeasure (bernoulliSeedLaw q h0 h1) := by
  unfold bernoulliSeedLaw
  infer_instance

theorem integral_bernoulliSeedLaw {bits : ℕ} (q : Fin bits → ℝ)
    (h0 : ∀ e, 0 ≤ q e) (h1 : ∀ e, q e ≤ 1) (f : Seed bits → ℝ) :
    (∫ r, f r ∂bernoulliSeedLaw q h0 h1) =
      bitsExpectation q Finset.univ (fun S => f (setSeed S)) := by
  classical
  rw [bernoulliSeedLaw, PMF.integral_eq_sum]
  simp only [seedPMF, PMF.ofFintype_apply, ENNReal.toReal_ofReal
    (bitsWeight_nonneg q h0 h1 _ _), smul_eq_mul]
  have h := (seedFinsetEquiv bits).sum_comp
    (fun S => bitsWeight q Finset.univ S * f (setSeed S))
  simpa only [seedFinsetEquiv, Equiv.coe_fn_mk, setSeed_seedSet,
    bitsExpectation, Finset.powerset_univ] using h

end MatroidProphet

end OAI
