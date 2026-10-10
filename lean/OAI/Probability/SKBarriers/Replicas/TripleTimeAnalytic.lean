import Mathlib
import OAI.Probability.SKBarriers.Replicas.TripleScaleStats
import OAI.Probability.SKBarriers.Scalar.SuffixPartitionSusceptibility
import OAI.Probability.SKBarriers.Replicas.TripleDecoupling
import OAI.Probability.SKBarriers.Replicas.TripleTimeBlocks
import OAI.Probability.SKBarriers.Hierarchy.WeightedBlockFactors
import OAI.Probability.SKBarriers.Hierarchy.TimeChainOnAnalytic

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

namespace TripleTimeBlocks
variable {α : ℝ → ℝ} {r s₁ s₂ q : ℝ} (B : TripleTimeBlocks α r s₁ s₂ q)

theorem full_mass (κ : ℝ) : ∀ p∈B.c++weightedUnderlying (B.w κ)++B.t,p.1∈Icc (0:ℝ) 1 := by
  rw [← B.full_raw κ]; exact B.full.raw_mass

theorem full_sorted (hm : Monotone α) (κ : ℝ) :
    (B.c++weightedUnderlying (B.w κ)++B.t).Pairwise (fun p q => p.1≤q.1) := by
  rw [← B.full_raw κ]; exact B.full.raw_sorted hm

theorem scalar_parisi (β : ℝ) (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α) (κ : ℝ) :
    scalarIncrementChain (scaleIncrementChain β (B.c++weightedUnderlying (B.w κ)++B.t)) scalarSpinTerminal 0-
      β^2/4*rawPenalty (B.c++weightedUnderlying (B.w κ)++B.t) 0=scalarCDFParisi β α := by
  rw [← B.full_raw κ,B.full.scalar_value β ha hm (by norm_num),B.full.penalty hm]
  simp only [sub_zero,Real.toNNReal_one,scalarCDFParisi,intervalIntegral.integral_of_le zero_le_one,
    ← integral_Icc_eq_integral_Ioc]
  ring

theorem scalar_root_hessian (β : ℝ) (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α) (κ : ℝ) :
    rootHessian 0 (scalarIncrementChain (scaleIncrementChain β (B.c++weightedUnderlying (B.w κ)++B.t)) scalarSpinTerminal) 0=
      scalarCDFHessian β α 0 1 0 := by
  rw [← B.full_raw κ,B.full.scalar_hessian β ha hm (by norm_num)]
  simp only [sub_zero,Real.toNNReal_one]

theorem scalar_susceptibility (β : ℝ) (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α)
    (hq : q∈Icc (0:ℝ) 1) (κ : ℝ) :
    tripleSusceptibility (scaleIncrementChain β B.c) (scaleIncrementChain β (B.w κ)) (scaleIncrementChain β B.t)=
      scalarCDFSusceptibilityAverage β α q := by
  have he : scaleIncrementChain β B.c++weightedUnderlying (scaleIncrementChain β (B.w κ))=
      scaleIncrementChain β (rawTimeChain B.front.chain) := by
    rw [B.prefix_raw κ,scaleIncrementChain_append,weightedUnderlying_scale]
  rw [tripleSusceptibility,he]
  exact B.front.scalar_susceptibility β ha hm hq B.tail

theorem tail_area (hm : Monotone α) : rawArea B.t=∫ x in q..1,α x := B.tail.area hm

theorem exists_scaled_factors (β : ℝ) {κ : ℝ} (hκ : 0≤κ) :
    ∃ k : Fin (zeroWeightChain (scaleIncrementChain β B.c)++scaleIncrementChain β (B.w κ)++zeroWeightChain (scaleIncrementChain β B.t)).length → ℝ,
      (∀ i,0≤k i) ∧
      (∀ i,((zeroWeightChain (scaleIncrementChain β B.c)++scaleIncrementChain β (B.w κ)++zeroWeightChain (scaleIncrementChain β B.t)).get i).2.2=
        k i*((zeroWeightChain (scaleIncrementChain β B.c)++scaleIncrementChain β (B.w κ)++zeroWeightChain (scaleIncrementChain β B.t)).get i).2.1) ∧
      (∀ i,k i≠0 → scalarPrefixVariance (zeroWeightChain (scaleIncrementChain β B.c)++scaleIncrementChain β (B.w κ)++zeroWeightChain (scaleIncrementChain β B.t)).length
        (fun j => ((zeroWeightChain (scaleIncrementChain β B.c)++scaleIncrementChain β (B.w κ)++zeroWeightChain (scaleIncrementChain β B.t)).get j).2.1) i.castSucc≤β^2*s₂) := by
  have he : zeroWeightChain (scaleIncrementChain β B.c)++scaleIncrementChain β (B.w κ)++zeroWeightChain (scaleIncrementChain β B.t)=
      zeroWeightChain (scaleIncrementChain β (B.c++B.b))++constantWeightChain κ (scaleIncrementChain β B.a)++
        zeroWeightChain (scaleIncrementChain β (B.d++B.t)) := by
    simp only [w,scaleIncrementChain_append,zeroWeightChain_scale,constantWeightChain_scale,zeroWeightChain_append,List.append_assoc]
  rw [he]
  refine ⟨blockWeights κ _ _ _,blockWeights_nonneg hκ _ _ _,blockWeights_factor κ _ _ _,?_⟩
  intro i hi
  have H := blockWeights_active κ (scaleIncrementChain β (B.c++B.b)) (scaleIncrementChain β B.a)
    (scaleIncrementChain β (B.d++B.t)) i hi
  rw [← scaleIncrementChain_append,rawVariance_scale,B.early_variance] at H
  exact H

end TripleTimeBlocks

end SK.Analytic

end
end

end OAI
