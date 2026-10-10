import Mathlib
import OAI.Probability.SKBarriers.Locking.NarrowScheduleEndpoint
import OAI.Probability.SKBarriers.Locking.NarrowTimeQuadratic
import OAI.Probability.SKBarriers.Locking.NarrowFiniteExpansion
import OAI.Probability.SKBarriers.Locking.NarrowBlockPenalty
import OAI.Probability.SKBarriers.Locking.NarrowTimeAnalytic

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

def narrowCDFTrialCoefficient (β : ℝ) (α : ℝ → ℝ) (r h q a θ : ℝ) : ℝ :=
  β^2*((2*a^2+θ^2)/h)*(scalarCDFSusceptibilityAverage β α q-(∫ x in q..1,α x))+
  2*narrowCDFMean β α r h θ*(β^2*a)*scalarCDFJointSusceptibility β α r q+
  narrowTentError (narrowCDFMean β α r h θ) (β^2*a) (β^2*θ) (α (r+h)-α (r-h))-
  β^2*(α r*(2*a*θ+θ^2)-a^2*(α (r+h)-α (r-h)))

namespace NarrowTimeBlocks
variable {α : ℝ → ℝ} {r h q : ℝ} (C : NarrowTimeBlocks α r h q)

include C in
theorem pressure_trial {N : ℕ} (hN : 0<N) (β δ : ℝ)
    (hα : ∀ z,α z∈Icc (0:ℝ) 1) (hmα : Monotone α)
    (hr : 0≤r) (hrq : r≤q) (hq : q≤1) (hh : 0<h)
    {a θ : ℝ} (ha : 0<a) (hθ : 0≤θ) (haθ : a+θ=1)
    (hD : Nonempty (MatrixStates N 3 (tripleGram r δ q)))
    {ε : ℝ} (hε : 0<ε) (hδ : 4*δ^2≤ε) (hδ1 : |δ|≤1)
    (hsmall : ε*(4*β^2*((2*a^2+θ^2)/h)+(2*β^2*(5*a+θ))^2)≤1/2) :
    matrixConstrainedPressure N 3 β (tripleGram r δ q)≤
      3*scalarCDFParisi β α+δ^2*narrowCDFTrialCoefficient β α r h q a θ+
      tripleExpansionConstant ε*|δ|^3+β^2*δ^4*((2*a^2+θ^2)/h)^2 := by
  have hn : h≠0 := ne_of_gt hh
  have hv : weightedUnderlying (C.v θ)=weightedUnderlying (C.w a) := by simp
  have Cs := C.cross_stats hn a θ
  have hy : weightedCross (C.c a)+weightedCross (C.w a)=0 := by rw [Cs.1,Cs.2.2]; ring
  have hg : weightedCross (C.c a)+weightedCross (C.v θ)=1 := by rw [Cs.1,Cs.2.1]; exact haθ
  have HP := narrowConstrainedPressure_schedule hN β δ (C.c a) (C.v θ) (C.w a) C.t hv hy
    (C.full_mass a) (C.full_sorted hmα a) (C.full_variance a) hg
    (by simpa only [C.common_variance,C.front_variance] using hD)
  rw [C.common_variance,C.front_variance] at HP
  change _≤vectorIncrementChain (scaleIncrementChain β (narrowSchedule δ (C.c a) (C.v θ) (C.w a) C.t)) _ _-_ -_+_ at HP
  rw [narrowSchedule_scale] at HP
  have he : weightedUnderlying (scaleIncrementChain β (C.c a))++weightedUnderlying (scaleIncrementChain β (C.w a))++scaleIncrementChain β C.t=
      scaleIncrementChain β (weightedUnderlying (C.c a)++weightedUnderlying (C.w a)++C.t) := by
    simp only [weightedUnderlying_scale,scaleIncrementChain_append]
  have hv' : weightedUnderlying (scaleIncrementChain β (C.v θ))=weightedUnderlying (scaleIncrementChain β (C.w a)) := by
    simp only [weightedUnderlying_scale,hv]
  have hs' : ε*(4*narrowVariance (scaleIncrementChain β (C.c a)) (scaleIncrementChain β (C.v θ)) (scaleIncrementChain β (C.w a))+
      (2*narrowAbsCross (scaleIncrementChain β (C.c a)) (scaleIncrementChain β (C.v θ)) (scaleIncrementChain β (C.w a)))^2)≤1/2 := by
    simpa only [narrowVariance_scale,C.variance_stats hn,narrowAbsCross_scale,C.absCross_stats hh ha.le hθ,mul_assoc] using hsmall
  have HE := narrowSchedule_value_expansion (scaleIncrementChain β (C.c a)) (scaleIncrementChain β (C.v θ))
    (scaleIncrementChain β (C.w a)) (scaleIncrementChain β C.t) hv'
    (by rw [he]; exact scaleIncrementChain_mass β _ (C.full_mass a))
    (by rw [he]; exact scaleIncrementChain_sorted β _ (C.full_sorted hmα a)) hε hδ hδ1 hs'
  rw [he] at HE
  have HQ := mul_le_mul_of_nonneg_left (C.quadratic_le β hα hmα hr hrq hq hh ha hθ) (sq_nonneg δ)
  have HC := mul_le_mul_of_nonneg_left (C.crossPenalty_lower hmα hh ha.le hθ) (show 0≤β^2*δ^2 by positivity)
  rw [C.variance_stats hn,C.tail_area hmα] at HP
  have HPar := C.scalar_parisi β hα hmα a
  unfold narrowCDFTrialCoefficient
  nlinarith only [HP,HE,HQ,HC,HPar]

end NarrowTimeBlocks

theorem narrowConstrainedPressure_quantile_trial {N k : ℕ} (hN : 0<N) (β δ : ℝ)
    (Q : Fin (k+1) → ℝ) (hQ : Q∈admissibleQuantiles k)
    {r h q a θ : ℝ} (hh : 0<h) (hhr : h≤r) (hhq : r+h≤q) (hq : q≤1)
    (ha : 0<a) (hθ : 0≤θ) (haθ : a+θ=1)
    (hD : Nonempty (MatrixStates N 3 (tripleGram r δ q)))
    {ε : ℝ} (hε : 0<ε) (hδ : 4*δ^2≤ε) (hδ1 : |δ|≤1)
    (hsmall : ε*(4*β^2*((2*a^2+θ^2)/h)+(2*β^2*(5*a+θ))^2)≤1/2) :
    matrixConstrainedPressure N 3 β (tripleGram r δ q)≤
      3*scalarCDFParisi β (quantileCDF k Q)+δ^2*narrowCDFTrialCoefficient β (quantileCDF k Q) r h q a θ+
      tripleExpansionConstant ε*|δ|^3+β^2*δ^4*((2*a^2+θ^2)/h)^2 := by
  obtain ⟨b⟩ := exists_quantile_TimeChainOn β Q hQ (s:=0) (t:=r-h) le_rfl (by linarith) (by linarith)
  obtain ⟨l⟩ := exists_quantile_TimeChainOn β Q hQ (s:=r-h) (t:=r) (by linarith) (by linarith) (by linarith)
  obtain ⟨j⟩ := exists_quantile_TimeChainOn β Q hQ (s:=r) (t:=r+h) (by linarith) (by linarith) (by linarith)
  obtain ⟨k'⟩ := exists_quantile_TimeChainOn β Q hQ (s:=r+h) (t:=q) (by linarith) hhq hq
  obtain ⟨t⟩ := exists_quantile_TimeChainOn β Q hQ (s:=q) (t:=1) (by linarith) hq le_rfl
  let C : NarrowTimeBlocks (quantileCDF k Q) r h q := ⟨b,l,j,k',t⟩
  exact C.pressure_trial hN β δ (quantileCDF_bounds k Q) (quantileCDF_monotone k Q)
    (by linarith) (by linarith) hq hh ha hθ haθ hD hε hδ hδ1 hsmall

end SK.Analytic

end
end

end OAI
