import Mathlib
import OAI.Probability.SKBarriers.Replicas.TripleContinuumTrial
import OAI.Probability.SKBarriers.Locking.TripleNegativeCoefficient

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem exists_tripleConstrainedPressure_gap {β : ℝ} (hβ : 0 < β)
    {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    ∃ μ : ProbabilityMeasure ℝ, (μ : Measure ℝ) (Icc (0:ℝ) 1)=1 ∧
      scalarCDFParisi β (cdf (μ : Measure ℝ))=finiteParisiInf β ∧
      ∃ τ r₀ δ₀ c : ℝ, 0 < τ ∧ 0 < r₀ ∧ 0 < δ₀ ∧ 0 < c ∧
        ∀ (N : ℕ), 0 < N → ∀ r δ q : ℝ,
          r ∈ Icc (0:ℝ) r₀ → |δ| ≤ δ₀ → q ∈ Icc h 1 →
          |q-scalarCDFOverlap β (cdf (μ : Measure ℝ)) q| ≤ τ →
          Nonempty (MatrixStates N 3 (tripleGram r δ q)) →
          matrixConstrainedPressure N 3 β (tripleGram r δ q) ≤ 3*finiteParisiInf β-c*δ^2 := by
  obtain ⟨μ,hμ,hmin,s₁,s₂,τ,r₀,c,hs₁,hs,hs₂,hτ,hr₀,hrs,hc,hC⟩ :=
    exists_negative_tripleCDF_coefficient hβ hh hh1
  let K := (s₂-s₁)⁻¹
  let M := 4*β^2*K+(2*β^2)^2
  obtain ⟨a,ha,hMa⟩ := continuousAt_small_interval
    (show ContinuousAt (fun a : ℝ => a*M) 0 by fun_prop)
    (show (0:ℝ)*M < 1/2 by norm_num) zero_lt_one
  have hsmall : a*M ≤ 1/2 := (hMa a ⟨ha.1.le,le_rfl⟩).le
  obtain ⟨d,hd,hda⟩ := continuousAt_small_interval
    (show ContinuousAt (fun d : ℝ => 4*d^2) 0 by fun_prop)
    (by simpa only [zero_pow (by decide : 2≠0),mul_zero] using ha.1) zero_lt_one
  obtain ⟨δ₀,hδ₀,hrem⟩ := continuousAt_small_interval
    (show ContinuousAt (fun x : ℝ => tripleExpansionConstant a*x+β^2*K^2*x^2) 0 by fun_prop)
    (by simpa only [zero_pow (by decide : 2≠0),mul_zero,add_zero] using half_pos hc) hd.1
  refine ⟨μ,hμ,hmin,τ,r₀,δ₀,c/2,hτ,hr₀,hδ₀.1,half_pos hc,?_⟩
  intro N hN r δ q hr hδ hq he hD
  have hδd : |δ| ≤ d := hδ.trans hδ₀.2.le
  have hδa : 4*δ^2 ≤ a := by
    have H := (hda |δ| ⟨abs_nonneg _,hδd⟩).le
    simpa only [sq_abs] using H
  have hδ1 : |δ| ≤ 1 := hδd.trans hd.2.le
  have H := tripleConstrainedPressure_continuum_trial hN β δ (cdf (μ : Measure ℝ))
    (fun z => ⟨cdf_nonneg _ _,cdf_le_one _ _⟩) (supported_probability_cdf_one μ hμ)
    hr.1 (hr.2.trans hrs.le) hs (hs₂.le.trans hq.1) hq.2 hD ha.1 hδa hδ1 hsmall
  rw [hmin] at H
  have HC := mul_le_mul_of_nonneg_left (hC r q hr hq he) (sq_nonneg δ)
  have HR := mul_le_mul_of_nonneg_left (hrem |δ| ⟨abs_nonneg _,hδ⟩).le (sq_nonneg δ)
  have HE : tripleExpansionConstant a*|δ|^3+β^2*δ^4*K^2 =
      δ^2*(tripleExpansionConstant a*|δ|+β^2*K^2*|δ|^2) := by
    conv_lhs => rw [show |δ|^3=|δ|^2*|δ| by ring,sq_abs]
    rw [sq_abs]
    ring
  change matrixConstrainedPressure N 3 β (tripleGram r δ q) ≤
    3*finiteParisiInf β+δ^2*tripleCDFTrialCoefficient β (cdf (μ : Measure ℝ)) K r s₁ s₂ q+
    tripleExpansionConstant a*|δ|^3+β^2*δ^4*K^2 at H
  have HR' : tripleExpansionConstant a*|δ|^3+β^2*δ^4*K^2 ≤ δ^2*(c/2) := by rw [HE]; exact HR
  nlinarith only [H,HC,HR']

end SK.Analytic

end
end

end OAI
