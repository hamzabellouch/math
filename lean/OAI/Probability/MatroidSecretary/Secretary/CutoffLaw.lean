import OAI.Probability.MatroidSecretary.Secretary.Coupling
import OAI.Probability.MatroidSecretary.Secretary.MaskLaw
import OAI.Probability.MatroidSecretary.Secretary.BinomialMixture

namespace OAI

/-!
# Actual initial branch/cutoff law

For the complete precommitted coupling seed, the initial branch and cutoff have
exactly the fair-branch/Binomial joint law in secretary.tex lines 54--66. This
averages the entire conditional table; it is not conditioning on the complete Q.
The cutoff is chosen before weights or arrival randomness. Empty/full cutoffs
and the empty ground set are included without exclusions.
-/

namespace MatroidProphet.Secretary
open MeasureTheory Finset
open scoped NNReal

/-- A statistic of the initial source component is unaffected by predrawing the
entire independent conditional table. No table entry is hidden or removed. -/
theorem integral_couplingSeedLaw_fst {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) (f : Seed (mainSeedBits n) → ℝ) :
    (∫ q : CouplingSeed n, f q.1 ∂couplingSeedLaw M hE) =
      ∫ r, f r ∂sourceSeedLaw n := by
  rw [couplingSeedLaw, integral_prod _ Integrable.of_finite]
  simp

/-- Exact branchwise Binomial law of the actual initial cutoff, not of a
reconstructed seed or a post-observation conditional full-Q distribution. -/
theorem integral_initial_branch_cutoff {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) (j : Bool) (f : ℕ → ℝ) :
    (∫ q : CouplingSeed n,
      (if mainBranch q.1 = j then f (couplingLength M hE q).val else 0)
      ∂couplingSeedLaw M hE) =
      (1 / 2 : ℝ) * ∑ k ∈ range (n + 1),
        (n.choose k : ℝ) * (branchRate j) ^ k *
          (1 - branchRate j) ^ (n - k) * f k := by
  change (∫ q : CouplingSeed n,
    (if mainBranch q.1 = j then f (sourceMask q.1).card else 0)
    ∂couplingSeedLaw M hE) = _
  rw [integral_couplingSeedLaw_fst M hE
      (fun r => if mainBranch r = j then f (sourceMask r).card else 0),
    integral_branch_sourceMask j (fun S => f S.card)]
  congr 1
  simpa only [Finset.card_univ, Fintype.card_fin] using
    SecretaryBinomialMixture.bitsExpectation_card (branchRate j)
      (univ : Finset (Fin n)) f

/-- The same actual-Q identity with the library Binomial probability measure. -/
theorem integral_initial_branch_cutoff_binomial {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) (j : Bool) (f : ℕ → ℝ) :
    (∫ q : CouplingSeed n,
      (if mainBranch q.1 = j then f (couplingLength M hE q).val else 0)
      ∂couplingSeedLaw M hE) =
      (1 / 2 : ℝ) * ∫ k,
        f k ∂ProbabilityTheory.binomial n
          ⟨branchRate j, (branchRate_pos j).le, (branchRate_lt_one j).le⟩ := by
  simp only [integral_initial_branch_cutoff, ProbabilityTheory.integral_binomial,
    smul_eq_mul, ← Nat.range_succ_eq_Iic]

/-- Real joint atoms of the actual initial branch and bounded cutoff. -/
theorem initial_branch_cutoff_atom_real {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) (j : Bool) (k : Fin (n + 1)) :
    (couplingSeedLaw M hE).real
      {q | mainBranch q.1 = j ∧ (couplingLength M hE q).val = k.val} =
      (1 / 2 : ℝ) * ((n.choose k.val : ℝ) * (branchRate j) ^ k.val *
        (1 - branchRate j) ^ (n - k.val)) := by
  classical
  rw [← integral_indicator_one (Set.to_countable _).measurableSet]
  have h := integral_initial_branch_cutoff M hE j
    (fun l => if l = k.val then (1 : ℝ) else 0)
  have hk : k.val ∈ range (n + 1) := mem_range.mpr k.isLt
  simpa [Set.indicator_apply, Pi.one_apply, ite_and, mul_ite, hk] using h

/-- The probability-measure version, retaining the branch factor one half. -/
theorem initial_branch_cutoff_atom {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) (j : Bool) (k : Fin (n + 1)) :
    couplingSeedLaw M hE
      {q | mainBranch q.1 = j ∧ (couplingLength M hE q).val = k.val} =
      ENNReal.ofReal ((1 / 2 : ℝ) * ((n.choose k.val : ℝ) *
        (branchRate j) ^ k.val * (1 - branchRate j) ^ (n - k.val))) := by
  rw [← initial_branch_cutoff_atom_real M hE j k, ofReal_measureReal]

end MatroidProphet.Secretary

end OAI
