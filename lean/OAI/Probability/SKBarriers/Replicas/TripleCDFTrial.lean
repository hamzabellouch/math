import Mathlib
import OAI.Probability.SKBarriers.Scalar.SuffixPartitionSusceptibility
import OAI.Probability.SKBarriers.Replicas.TripleTimeBlocks
import OAI.Probability.SKBarriers.Replicas.TripleTimeAnalytic
import OAI.Probability.SKBarriers.Replicas.TripleQuadraticPressure

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

def tripleTimeCommonError (β K r : ℝ) : ℝ :=
  2*(2*β^2*K+(2*β^2)^2)*((susceptibilityLipschitzConstant:ℝ)+2*Real.exp 2)*
    Real.sqrt (2*(β^2*r)+4*(β^2*r)^2)

def tripleCDFResponse (β : ℝ) (α : ℝ → ℝ) (s q : ℝ) : ℝ :=
  β^2*scalarCDFSusceptibilityAverage β α q*
    (scalarCDFHessian β α 0 1 0+2*(β^2*s)+4*(β^2*s)^2)-1

def tripleCDFTrialCoefficient (β : ℝ) (α : ℝ → ℝ) (K r s₁ s₂ q : ℝ) : ℝ :=
  β^2*K*(scalarCDFSusceptibilityAverage β α q-(∫ x in q..1,α x))+
    β^2*(α s₁*tripleCDFResponse β α s₂ q+max (tripleCDFResponse β α s₂ q) 0)+
    tripleTimeCommonError β K r

theorem crossPenalty_response_le {J m : ℝ} (hm : 0 ≤ m) (hJ : J∈Icc m 1) (T : ℝ) :
    J*T ≤ m*T+max T 0 := by
  by_cases hT : 0 ≤ T
  · rw [max_eq_left hT]
    have H := mul_le_mul_of_nonneg_right hJ.2 hT
    have H' := mul_nonneg hm hT
    linarith
  · rw [max_eq_right (le_of_not_ge hT),add_zero]
    exact mul_le_mul_of_nonpos_right hJ.1 (le_of_not_ge hT)

namespace TripleTimeBlocks
variable {α : ℝ → ℝ} {r s₁ s₂ q : ℝ} (B : TripleTimeBlocks α r s₁ s₂ q)

theorem common_error (β : ℝ) (hs : s₁ < s₂) :
    tripleCommonError (scaleIncrementChain β B.c) (scaleIncrementChain β (B.w (s₂-s₁)⁻¹))=
      tripleTimeCommonError β (s₂-s₁)⁻¹ r := by
  rcases B.normalized_stats hs with ⟨hK,_,hC⟩
  simp only [tripleCommonError,weightedMomentBound,weightedVariance_scale,weightedAbsCross_scale,
    rawVariance_scale,hK,hC,B.c_variance,mul_one,tripleTimeCommonError]
  ring

theorem coefficient_le (β : ℝ) (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α)
    (hq : q∈Icc (0:ℝ) 1) (hs : s₁ < s₂) :
    tripleQuadraticCoefficient β (β^2*s₂) B.c (B.w (s₂-s₁)⁻¹) B.t ≤
      tripleCDFTrialCoefficient β α (s₂-s₁)⁻¹ r s₁ s₂ q := by
  rcases B.normalized_stats hs with ⟨hK,_,hC⟩
  unfold tripleQuadraticCoefficient
  rw [B.scalar_susceptibility β ha hm hq,B.scalar_root_hessian β ha hm,
    B.tail_area hm,hK,B.common_error β hs]
  unfold tripleCDFTrialCoefficient
  change _+β^2*weightedCrossPenalty (B.w (s₂-s₁)⁻¹) 0*tripleCDFResponse β α s₂ q+_ ≤ _
  have H := mul_le_mul_of_nonneg_left (crossPenalty_response_le (ha s₁).1
    (B.normalized_penalty hm hs) (tripleCDFResponse β α s₂ q)) (sq_nonneg β)
  linarith

include B in
theorem pressure_trial {N : ℕ} (hN : 0 < N) (β δ : ℝ)
    (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α) (hq : q∈Icc (0:ℝ) 1) (hs : s₁ < s₂)
    (hD : Nonempty (MatrixStates N 3 (tripleGram r δ q)))
    {a : ℝ} (ha0 : 0 < a) (hδ : 4*δ^2 ≤ a) (hδ1 : |δ| ≤ 1)
    (hsmall : a*(4*β^2*(s₂-s₁)⁻¹+(2*β^2)^2) ≤ 1/2) :
    matrixConstrainedPressure N 3 β (tripleGram r δ q) ≤
      3*scalarCDFParisi β α+δ^2*tripleCDFTrialCoefficient β α (s₂-s₁)⁻¹ r s₁ s₂ q+
      tripleExpansionConstant a*|δ|^3+β^2*δ^4*((s₂-s₁)⁻¹)^2 := by
  rcases B.normalized_stats hs with ⟨hK,hC,hA⟩
  obtain ⟨k,hk,he,hactive⟩ := B.exists_scaled_factors β (inv_nonneg.mpr (sub_pos.mpr hs).le)
  have hs₂ : 0 ≤ s₂ := by have H := B.early.sub_nonneg; simpa only [sub_zero] using H
  have H := tripleConstrainedPressure_quadratic hN β δ B.c (B.w (s₂-s₁)⁻¹) B.t
    (B.full_mass _) (B.full_sorted hm _) (B.full_variance _) hC
    (by simpa only [B.c_variance,B.prefix_variance] using hD) k hk he
    (mul_nonneg (sq_nonneg β) hs₂) hactive ha0 hδ hδ1 (by simpa only [hK,hA,mul_one] using hsmall)
  rw [B.c_variance,B.prefix_variance,B.scalar_parisi β ha hm,hK] at H
  have HC := mul_le_mul_of_nonneg_left (B.coefficient_le β ha hm hq hs) (sq_nonneg δ)
  linarith

end TripleTimeBlocks

theorem tripleConstrainedPressure_quantile_trial {N k : ℕ} (hN : 0 < N) (β δ : ℝ)
    (Q : Fin (k+1) → ℝ) (hQ : Q∈admissibleQuantiles k)
    {r s₁ s₂ q : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s₁) (hs : s₁ < s₂) (hsq : s₂ ≤ q) (hq : q ≤ 1)
    (hD : Nonempty (MatrixStates N 3 (tripleGram r δ q)))
    {a : ℝ} (ha : 0 < a) (hδ : 4*δ^2 ≤ a) (hδ1 : |δ| ≤ 1)
    (hsmall : a*(4*β^2*(s₂-s₁)⁻¹+(2*β^2)^2) ≤ 1/2) :
    matrixConstrainedPressure N 3 β (tripleGram r δ q) ≤
      3*scalarCDFParisi β (quantileCDF k Q)+
      δ^2*tripleCDFTrialCoefficient β (quantileCDF k Q) (s₂-s₁)⁻¹ r s₁ s₂ q+
      tripleExpansionConstant a*|δ|^3+β^2*δ^4*((s₂-s₁)⁻¹)^2 := by
  obtain ⟨c⟩ := exists_quantile_TimeChainOn β Q hQ (s:=0) (t:=r) le_rfl hr (by linarith)
  obtain ⟨b⟩ := exists_quantile_TimeChainOn β Q hQ hr hrs (by linarith)
  obtain ⟨a'⟩ := exists_quantile_TimeChainOn β Q hQ (show 0 ≤ s₁ by linarith) hs.le (by linarith)
  obtain ⟨d⟩ := exists_quantile_TimeChainOn β Q hQ (show 0 ≤ s₂ by linarith) hsq hq
  obtain ⟨t⟩ := exists_quantile_TimeChainOn β Q hQ (show 0 ≤ q by linarith) hq le_rfl
  let B : TripleTimeBlocks (quantileCDF k Q) r s₁ s₂ q := ⟨c,b,a',d,t⟩
  exact B.pressure_trial hN β δ (quantileCDF_bounds k Q) (quantileCDF_monotone k Q)
    ⟨by linarith,hq⟩ hs hD ha hδ hδ1 hsmall

end SK.Analytic

end
end

end OAI
