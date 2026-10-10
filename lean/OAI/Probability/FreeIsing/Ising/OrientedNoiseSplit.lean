import OAI.Probability.FreeIsing.Ising.CopyResponseRowPaths
import OAI.Probability.FreeIsing.Ising.OrientedPrefixWeights

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingOrientedPath
open IsingObservationInnovation IsingObservationFactor IsingCopySpectral
open IsingCopyPathBounds IsingCopyWeightedCut

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

def weightedLogEnergy (hb : 0 ≤ beta) (t : ℝ≥0) (inward : Bool)
    (v : TreeVertex d) (s : Finset ℕ) (left : Bool) : ℝ :=
  ∫ q, logSum hb t inward v s q ^ 2 *
    attenuation hb t inward v (observationCopy left q) ^ 2 ∂copies beta μ

theorem integrable_weightedLog
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (inward : Bool) (v : TreeVertex d) (s : Finset ℕ) (left : Bool) :
    Integrable (fun q => logSum hb t inward v s q ^ 2 *
      attenuation hb t inward v (observationCopy left q) ^ 2) (copies beta μ) := by
  apply (integrable_pathLogDifference_sq hμ hb t s (edge inward v)).mul_bdd
    (((measurable_attenuation hb t inward v).comp
      (measurable_observationCopy left)).pow_const 2).aestronglyMeasurable
  filter_upwards [] with q
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_one₀ (attenuation_mem_Icc hb t inward v _).1
    (attenuation_mem_Icc hb t inward v _).2

theorem logSum_split (hb : 0 ≤ beta) (t : ℝ≥0) (inward : Bool)
    (v : TreeVertex d) {p : ℕ} (hp : p ≤ v.1.length)
    (q : IsingConditionalCopyBounds.CopySpace d) :
    logSum hb t inward v (Finset.range v.1.length) q =
      logSum hb t inward v (Finset.range p) q +
      logSum hb t inward v (Finset.Ico p v.1.length) q :=
  (Finset.sum_range_add_sum_Ico
    (fun i => edgeLogDifference hb t (edge inward v i).1 (edge inward v i).2 q) hp).symm

theorem weightedLogEnergy_split_le
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (inward : Bool) (v : TreeVertex d) {p : ℕ}
    (hp : p ≤ v.1.length) (left : Bool) :
    weightedLogEnergy (μ := μ) hb t inward v (Finset.range v.1.length) left ≤
      2 * (weightedLogEnergy (μ := μ) hb t inward v (Finset.range p) left +
        weightedLogEnergy (μ := μ) hb t inward v (Finset.Ico p v.1.length) left) := by
  have hi₁ := integrable_weightedLog hμ hb t inward v (Finset.range p) left
  have hi₂ := integrable_weightedLog hμ hb t inward v (Finset.Ico p v.1.length) left
  have hall := integrable_weightedLog hμ hb t inward v (Finset.range v.1.length) left
  unfold weightedLogEnergy
  rw [← integral_add hi₁ hi₂, ← integral_const_mul]
  apply integral_mono hall ((hi₁.add hi₂).const_mul 2)
  intro q
  dsimp only [Pi.add_apply]
  rw [logSum_split hb t inward v hp q]
  have hs : (logSum hb t inward v (Finset.range p) q +
      logSum hb t inward v (Finset.Ico p v.1.length) q) ^ 2 ≤
      2 * (logSum hb t inward v (Finset.range p) q ^ 2 +
        logSum hb t inward v (Finset.Ico p v.1.length) q ^ 2) := by
    nlinarith [sq_nonneg (logSum hb t inward v (Finset.range p) q -
      logSum hb t inward v (Finset.Ico p v.1.length) q)]
  calc
    _ ≤ (2 * (logSum hb t inward v (Finset.range p) q ^ 2 +
        logSum hb t inward v (Finset.Ico p v.1.length) q ^ 2)) *
      attenuation hb t inward v (observationCopy left q) ^ 2 :=
        mul_le_mul_of_nonneg_right hs (sq_nonneg _)
    _ = _ := by ring

theorem noiseEnergy_eq_weightedLogEnergy
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) :
    IsingCopyResponseRowPaths.noiseEnergy (μ := μ) hb t v =
      weightedLogEnergy (μ := μ) hb t false v (Finset.range v.1.length) true +
      weightedLogEnergy (μ := μ) hb t false v (Finset.range v.1.length) false := by
  rw [weightedLogEnergy, weightedLogEnergy, ← integral_add
    (integrable_weightedLog hμ hb t false v (Finset.range v.1.length) true)
    (integrable_weightedLog hμ hb t false v (Finset.range v.1.length) false)]
  apply integral_congr_ae
  filter_upwards [] with q
  change (attenuation hb t false v (observationCopy true q) ^ 2 +
      attenuation hb t false v (observationCopy false q) ^ 2) *
      logSum hb t false v (Finset.range v.1.length) q ^ 2 = _
  ring

theorem noiseEnergy_le_four_half_weights
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) {p : ℕ} (hp : p ≤ v.1.length) :
    IsingCopyResponseRowPaths.noiseEnergy (μ := μ) hb t v ≤ 2 *
      (weightedLogEnergy (μ := μ) hb t false v (Finset.range p) true +
       weightedLogEnergy (μ := μ) hb t false v (Finset.range p) false +
       weightedLogEnergy (μ := μ) hb t false v (Finset.Ico p v.1.length) true +
       weightedLogEnergy (μ := μ) hb t false v (Finset.Ico p v.1.length) false) := by
  rw [noiseEnergy_eq_weightedLogEnergy hμ hb t v]
  have hl := weightedLogEnergy_split_le hμ hb t false v hp true
  have hr := weightedLogEnergy_split_le hμ hb t false v hp false
  linarith

end Problem367.IsingOrientedPath

end

end OAI
