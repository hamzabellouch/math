import OAI.Probability.GammaPassage.FiniteEdgeTilt

namespace OAI

namespace GammaFPP.Tilt
open Real MeasureTheory ProbabilityTheory PlanarFPP GammaFPP.Grid

/-- A shape-dependent exponential envelope for the Gamma likelihood moment. -/
lemma gamma_likelihood_envelope {shape : ℝ} (hs : 0 < shape)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/2) (M : ℕ) :
    (1-δ^2)^(-shape*(M : ℝ)) ≤ exp (2*shape*M*δ^2) := by
  have hden : 0 < 1-δ^2 := by nlinarith
  have hsmall : 0 ≤ 1-2*δ^2 := by nlinarith
  have hrat : 1/(1-δ^2) ≤ 2*δ^2+1 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg (sq_nonneg δ) hsmall]
  have he := hrat.trans (add_one_le_exp (2*δ^2))
  have hl := Real.log_le_log (by positivity : 0 < 1/(1-δ^2)) he
  rw [one_div, Real.log_inv, Real.log_exp] at hl
  have hm := mul_le_mul_of_nonneg_left hl
    (mul_nonneg hs.le (Nat.cast_nonneg M))
  rw [Real.rpow_def_of_pos hden]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem finite_edge_tilt_probability_sq_exp_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}
    {shape rate : ℝ} (h : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate)
    (S : Finset Edge) (δ : ℝ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/2)
    (A : Set (Edge → ℝ)) (hA : MeasurableSet A) (hS : DependsOnEdges A S) :
    P.real {ω | scaleFiniteEdges S (1-δ) (fun e => τ e ω) ∈ A} ^ 2 ≤
      exp (2*shape*S.card*δ^2) * P.real {ω | (fun e => τ e ω) ∈ A} := by
  exact (finite_edge_tilt_probability_sq_bound h hs hr S δ (by linarith) (by linarith)
    A hA hS).trans (mul_le_mul_of_nonneg_right
      (gamma_likelihood_envelope hs δ hδ hδ' S.card) measureReal_nonneg)

end GammaFPP.Tilt

end OAI
