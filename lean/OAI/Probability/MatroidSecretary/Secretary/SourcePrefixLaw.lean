import OAI.Probability.MatroidSecretary.Secretary.PrefixObservationModel
import OAI.Probability.MatroidSecretary.Secretary.SourceMask
import OAI.Probability.MatroidSecretary.Secretary.Prefix
import OAI.Probability.MatroidSecretary.Secretary.BinomialMixture
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-!
# The concrete source observation law after a uniform random prefix

The initially sampled source seed determines the branch and prefix length.
An independent uniform permutation supplies the actual observed prefix.
Averaging the length, rather than conditioning on the complete initial seed,
recovers the full joint law of the branch and sacrificed source mask.

This is the actual source-law input to conditional-table reconstruction in
`sections/secretary.tex`, equations `eq:secretary-prefix-mask` and its following
kernel argument (SHA256
`3554fe0f7296782edf63cc7f1305c377e7a7b9d8f8948b9510ea4ad02a702d63`).
It does not assume a caller-given source transport law.
-/

namespace MatroidProphet.Secretary

open MeasureTheory Finset

/-- A predrawn Bernoulli mask supplies only the length; the independent random
prefix has the original product-mask law after averaging that length. -/
theorem predrawn_mask_prefix_integral {n : ℕ} (p : ℝ)
    (f : Finset (Fin n) → ℝ) :
    bitsExpectation (fun _ : Fin n => p) univ (fun B =>
      ∫ σ : ArrivalOrder n,
        f (univ.filter fun e : Fin n => (σ.symm e).val < B.card)
        ∂(PMF.uniformOfFintype (ArrivalOrder n)).toMeasure) =
      bitsExpectation (fun _ : Fin n => p) univ f := by
  have hB (B : Finset (Fin n)) :
      (∫ σ : ArrivalOrder n,
        f (univ.filter fun e : Fin n => (σ.symm e).val < B.card)
        ∂(PMF.uniformOfFintype (ArrivalOrder n)).toMeasure) =
      (∑ S ∈ (univ : Finset (Fin n)).powersetCard B.card, f S) /
        Nat.choose n B.card :=
    integral_uniform_prefix (by simpa using Finset.card_le_univ B) f
  simp_rw [hB]
  simpa only [Finset.card_univ, Fintype.card_fin, div_eq_mul_inv, mul_comm] using
    SecretaryBinomialMixture.predrawn_card_uniform_subset p (univ : Finset (Fin n)) f

/-- Exact test-function identity for the manuscript's concrete full source seed.
The branch, prefix length and every unused source coin are sampled before the
independent uniform permutation. -/
theorem integral_source_random_prefix {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) (f : Bool → Finset (Fin n) → ℝ) :
    (∫ r, ∫ σ : ArrivalOrder n,
      f (mainBranch r)
        (univ.filter fun e : Fin n =>
          (σ.symm e).val < ((completeHiddenRule M hE).mask r).card)
      ∂(PMF.uniformOfFintype (ArrivalOrder n)).toMeasure ∂sourceSeedLaw n) =
      ∫ r, f (mainBranch r) ((completeHiddenRule M hE).mask r) ∂sourceSeedLaw n := by
  rw [integral_source_branch_mask M hE (fun j B =>
    ∫ σ : ArrivalOrder n,
      f j (univ.filter fun e : Fin n => (σ.symm e).val < B.card)
      ∂(PMF.uniformOfFintype (ArrivalOrder n)).toMeasure)]
  rw [integral_source_branch_mask M hE f]
  simp_rw [predrawn_mask_prefix_integral]

/-- The full branch/prefix pushforward equals the branch/sacrificed-mask law of
our concrete source algorithm. This is the exact input used by the finite
conditional-table reconstruction, including empty and full prefixes. -/
theorem source_random_prefix_joint_law {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) :
    ((sourceSeedLaw n).prod
      (PMF.uniformOfFintype (ArrivalOrder n)).toMeasure).map
      (fun z : Seed (mainSeedBits n) × ArrivalOrder n =>
        (mainBranch z.1, orderPrefix z.2 ((completeHiddenRule M hE).mask z.1).card)) =
      (sourceSeedLaw n).map
        (fun r => (mainBranch r, (completeHiddenRule M hE).mask r)) := by
  classical
  let index : Seed (mainSeedBits n) × ArrivalOrder n → Bool × Finset (Fin n) :=
    fun z => (mainBranch z.1, orderPrefix z.2 ((completeHiddenRule M hE).mask z.1).card)
  let obs : Seed (mainSeedBits n) → Bool × Finset (Fin n) :=
    fun r => (mainBranch r, (completeHiddenRule M hE).mask r)
  let μ := (sourceSeedLaw n).prod (PMF.uniformOfFintype (ArrivalOrder n)).toMeasure
  have htest (f : Bool × Finset (Fin n) → ℝ) :
      (∫ z, f (index z) ∂μ) = ∫ r, f (obs r) ∂sourceSeedLaw n := by
    rw [integral_prod _ Integrable.of_finite]
    simpa only [index, obs, orderPrefix] using
      integral_source_random_prefix M hE (fun j P => f (j, P))
  change μ.map index = (sourceSeedLaw n).map obs
  apply Measure.ext_of_singleton
  intro b
  have hreal : (μ.map index).real {b} = ((sourceSeedLaw n).map obs).real {b} := by
    rw [← integral_indicator_one (measurableSet_singleton b),
      ← integral_indicator_one (measurableSet_singleton b)]
    rw [integral_map_of_stronglyMeasurable (measurable_of_countable index)
      (measurable_of_countable _).stronglyMeasurable,
      integral_map_of_stronglyMeasurable (measurable_of_countable obs)
      (measurable_of_countable _).stronglyMeasurable]
    exact htest _
  calc
    μ.map index {b} = ENNReal.ofReal ((μ.map index).real {b}) :=
      (ofReal_measureReal).symm
    _ = ENNReal.ofReal (((sourceSeedLaw n).map obs).real {b}) :=
      congrArg ENNReal.ofReal hreal
    _ = (sourceSeedLaw n).map obs {b} := ofReal_measureReal

end MatroidProphet.Secretary

end OAI
