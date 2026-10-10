import Mathlib
import OAI.Probability.SKBarriers.Locking.NarrowCDFTrial
import OAI.Probability.SKBarriers.Replicas.TripleContinuumTrial

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem intervalCDFArea_eq_sub_tail {α : ℝ → ℝ} (hα : Monotone α) (r s : ℝ) :
    (∫ z in r..s,α z)=(∫ z in r..1,α z)-(∫ z in s..1,α z) := by
  have H := intervalIntegral.integral_add_adjacent_intervals (a:=r) (b:=s) (c:=1) (μ:=volume)
    hα.intervalIntegrable hα.intervalIntegrable
  linarith

theorem narrowCDFMean_tendsto (β r h θ : ℝ) {α : ℝ → ℝ} {αn : ℕ → ℝ → ℝ}
    (hα : Monotone α) (hn : ∀ n,Monotone (αn n))
    (hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0))
    (hr : r∈Icc (0:ℝ) 1) (hs : r+h∈Icc (0:ℝ) 1) :
    Tendsto (fun n => narrowCDFMean β (αn n) r h θ) atTop (𝓝 (narrowCDFMean β α r h θ)) := by
  simp only [narrowCDFMean,intervalCDFArea_eq_sub_tail hα r (r+h),intervalCDFArea_eq_sub_tail (hn _) r (r+h)]
  exact ((cdfArea_tendsto hα hn hD hr).sub (cdfArea_tendsto hα hn hD hs)).const_mul _

theorem narrowCDFTrialCoefficient_uniform_tendsto (β : ℝ) (α : StieltjesFunction ℝ)
    (hα : ∀ z,α z∈Icc (0:ℝ) 1) (hα1 : α 1=1)
    {r h q : ℝ} (hh : 0<h) (hhr : h≤r) (hhq : r+h≤q) (hq : q≤1) (a θ : ℝ) :
    Tendsto (fun n => narrowCDFTrialCoefficient β (quantileCDF n (uniformCDFQuantiles n α)) r h q a θ) atTop
      (𝓝 (narrowCDFTrialCoefficient β α r h q a θ)) := by
  let αn := fun n => quantileCDF n (uniformCDFQuantiles n α)
  have hn (n z) : αn n z∈Icc (0:ℝ) 1 := quantileCDF_bounds n _ z
  have hnm (n) : Monotone (αn n) := quantileCDF_monotone n _
  have hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0) := uniformCDFQuantiles_L1_tendsto α hα hα1
  have hχ := scalarCDFSusceptibilityAverage_tendsto β hα α.mono hn hnm hD (r:=q) ⟨by linarith,hq⟩
  have hA := cdfArea_tendsto α.mono hnm hD (q:=q) ⟨by linarith,hq⟩
  have hJ := scalarCDFJointSusceptibility_tendsto β hα α.mono hn hnm hD
    (r:=r) (q:=q) (by linarith) (by linarith) hq
  have hM := narrowCDFMean_tendsto β r h θ α.mono hnm hD ⟨by linarith,by linarith⟩ ⟨by linarith,by linarith⟩
  have hrA := uniformCDFQuantiles_pointwise_tendsto α hα hα1 (s:=r) ⟨by linarith,by linarith⟩
  have hω := (uniformCDFQuantiles_pointwise_tendsto α hα hα1 (s:=r+h) ⟨by linarith,by linarith⟩).sub
    (uniformCDFQuantiles_pointwise_tendsto α hα hα1 (s:=r-h) ⟨by linarith,by linarith⟩)
  have hE : Tendsto (fun n => narrowTentError (narrowCDFMean β (αn n) r h θ) (β^2*a) (β^2*θ) (αn n (r+h)-αn n (r-h))) atTop
      (𝓝 (narrowTentError (narrowCDFMean β α r h θ) (β^2*a) (β^2*θ) (α (r+h)-α (r-h)))) := by
    exact (((tendsto_const_nhds.add (((hM.const_mul 2).mul_const (β^2*a)).mul hω)).add
      ((hω.const_mul (β^2*a)).pow 2)).add (hω.const_mul ((β^2*a)^2)))
  exact ((((hχ.sub hA).const_mul (β^2*((2*a^2+θ^2)/h))).add
    (((hM.const_mul 2).mul_const (β^2*a)).mul hJ)).add hE).sub
      (((hrA.mul_const (2*a*θ+θ^2)).sub (hω.const_mul (a^2))).const_mul (β^2))

theorem narrowConstrainedPressure_continuum_trial {N : ℕ} (hN : 0<N) (β δ : ℝ)
    (α : StieltjesFunction ℝ) (hα : ∀ z,α z∈Icc (0:ℝ) 1) (hα1 : α 1=1)
    {r h q a θ : ℝ} (hh : 0<h) (hhr : h≤r) (hhq : r+h≤q) (hq : q≤1)
    (ha : 0<a) (hθ : 0≤θ) (haθ : a+θ=1)
    (hD : Nonempty (MatrixStates N 3 (tripleGram r δ q)))
    {ε : ℝ} (hε : 0<ε) (hδ : 4*δ^2≤ε) (hδ1 : |δ|≤1)
    (hsmall : ε*(4*β^2*((2*a^2+θ^2)/h)+(2*β^2*(5*a+θ))^2)≤1/2) :
    matrixConstrainedPressure N 3 β (tripleGram r δ q)≤
      3*scalarCDFParisi β α+δ^2*narrowCDFTrialCoefficient β α r h q a θ+
      tripleExpansionConstant ε*|δ|^3+β^2*δ^4*((2*a^2+θ^2)/h)^2 := by
  have hC := narrowCDFTrialCoefficient_uniform_tendsto β α hα hα1 hh hhr hhq hq a θ
  have hP := scalarCDFParisi_tendsto_of_L1 β hα α.mono
    (fun n => quantileCDF_bounds n (uniformCDFQuantiles n α))
    (fun n => quantileCDF_monotone n (uniformCDFQuantiles n α)) (uniformCDFQuantiles_L1_tendsto α hα hα1)
  apply ge_of_tendsto ((((hP.const_mul 3).add (hC.const_mul (δ^2))).add_const
    (tripleExpansionConstant ε*|δ|^3)).add_const (β^2*δ^4*((2*a^2+θ^2)/h)^2))
  exact Eventually.of_forall (fun n => narrowConstrainedPressure_quantile_trial hN β δ
    (uniformCDFQuantiles n α) (uniformCDFQuantiles_admissible n α hα1) hh hhr hhq hq ha hθ haθ hD hε hδ hδ1 hsmall)

end SK.Analytic

end
end

end OAI
