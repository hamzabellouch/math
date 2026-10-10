import OAI.Analysis.LiebThirring.WeightedCutoff

namespace OAI


noncomputable section
namespace SharpLiebThirring.OperatorProof
open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction

def localSqrt (W : ℝ → ℝ) (R : ℝ) : ℝ → ℂ :=
  (Interval R).indicator (fun x ↦ (Real.sqrt ‖W x‖ : ℂ))

lemma localSqrt_memLp {W : ℝ → ℝ} (hW : LocallyIntegrable W volume) (R : ℝ) :
    MemLp (localSqrt W R) 2 volume := by
  have hm : AEStronglyMeasurable (localSqrt W R) volume :=
    ((Complex.continuous_ofReal.comp Real.continuous_sqrt).comp_aestronglyMeasurable
      hW.aestronglyMeasurable.norm).indicator measurableSet_Icc
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have hi : Integrable ((Interval R).indicator (fun x ↦ ‖W x‖)) volume :=
    IntegrableOn.integrable_indicator
    (s := Interval R) (hW.integrableOn_isCompact isCompact_Icc).norm measurableSet_Icc
  apply hi.congr
  filter_upwards [] with x
  symm
  by_cases hx : x ∈ Interval R
  · simp only [localSqrt,indicator_of_mem hx,Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (norm_nonneg _)]
  · simp only [localSqrt,indicator_of_notMem hx,norm_zero,zero_pow (by decide : 2 ≠ 0)]

def localWeightedL {W : ℝ → ℝ} (d : PotentialData W) (R : ℝ) : H1C →L[ℂ] L2C :=
  (cutoffL (Interval R) measurableSet_Icc).comp (weightedL d)

lemma localWeightedL_ae {W : ℝ → ℝ} (d : PotentialData W) (R : ℝ) (u : H1C) :
    localWeightedL d R u =ᵐ[volume] (fun x ↦ localSqrt W R x * valL u x) := by
  filter_upwards [cutoffL_ae (Interval R) measurableSet_Icc (weightedL d u),
    (weightedVal_memLp d u).coeFn_toLp] with x hx hy
  change localWeightedL d R u x = (Interval R).indicator (weightedL d u) x at hx
  change weightedL d u x = weightedVal d u x at hy
  rw [hx]
  by_cases hs : x ∈ Interval R
  · simp only [indicator_of_mem hs,localSqrt,hy,weightedVal]
  · simp only [indicator_of_notMem hs,localSqrt,zero_mul]

lemma localWeightedL_compact {W : ℝ → ℝ} (d : PotentialData W)
    (hW : LocallyIntegrable W volume) {R : ℝ} (hR : 0 ≤ R) :
    IsCompactOperator (localWeightedL d R) := by
  have he : (fun u : H1C ↦ localWeightedL d R u) =
      (fun u : H1C ↦ weightedBCF hR (localSqrt_memLp hW R) (localRep R u)) := by
    funext u
    apply Lp.ext
    exact (localWeightedL_ae d R u).trans
      (weightedBCF_localRep_ae hR (localSqrt_memLp hW R)
        (fun x hx ↦ by simp only [localSqrt,indicator_of_notMem hx]) u).symm
  rw [show (localWeightedL d R : H1C → L2C) = _ from he]
  exact weightedBCF_localRep_isCompact hR (localSqrt_memLp hW R)

end SharpLiebThirring.OperatorProof

end

end OAI
