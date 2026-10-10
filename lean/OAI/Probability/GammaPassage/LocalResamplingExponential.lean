import OAI.Probability.GammaPassage.LocalResamplingModel
import OAI.Probability.GammaPassage.ExponentialIncrement
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace OAI

namespace GammaFPP.FiniteLocal
open MeasureTheory ProbabilityTheory PlanarFPP Real Finset
open scoped ENNReal

/-- A single minimizing trail bounds the summed upward resampling increments
for every replacement law supported on nonnegative weights. -/
theorem sum_upward_transform (μ : Measure ℝ) (hμ : ∀ᵐ u ∂μ, 0 ≤ u)
    (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e) (p q : Vertex) (R : ℕ)
    (hR : latticeDistance p q < R) (φ : ℝ → ℝ≥0∞)
    (hφ : MonotoneOn φ (Set.Ici 0)) (hzero : φ 0 = 0) :
    (∑ e ∈ localEdges p q R, ∫⁻ u, φ (upward w p q R e u) ∂μ) ≤
      (∫⁻ u, φ u ∂μ) * R := by
  classical
  obtain ⟨ds, hds, hm⟩ := minimizing_candidate w p q R hR
  obtain ⟨hend, hn, hl⟩ := (mem_candidates p q R ds).mp hds
  have hsub := candidate_edges_subset p q R ds hds
  have he : ∀ e, (∫⁻ u, φ (upward w p q R e u) ∂μ) ≤
      if e ∈ (trace p ds).map traversalEdge then ∫⁻ u, φ u ∂μ else 0 := by
    intro e
    by_cases he : e ∈ (trace p ds).map traversalEdge
    · rw [ite_eq_left he]
      apply lintegral_mono_ae
      filter_upwards [hμ] with u hu
      apply hφ (upward_nonneg w p q R e u) hu
      simpa only [ite_eq_left he] using upward_le w hw p q R ds hds hm e u hu
    · rw [ite_eq_right he, ← lintegral_zero (μ := μ)]
      apply lintegral_mono_ae
      filter_upwards [hμ] with u hu
      have hb := upward_le w hw p q R ds hds hm e u hu
      simp only [ite_eq_right he] at hb
      rw [le_antisymm hb (upward_nonneg w p q R e u), hzero]
  calc
    _ ≤ ∑ e ∈ localEdges p q R,
        if e ∈ (trace p ds).map traversalEdge then ∫⁻ u, φ u ∂μ else 0 :=
      Finset.sum_le_sum (fun e _ => he e)
    _ = ∑ e ∈ ((trace p ds).map traversalEdge).toFinset, ∫⁻ u, φ u ∂μ := by
      rw [← Finset.sum_filter]
      congr 1
      ext e
      simp only [Finset.mem_filter, List.mem_toFinset]
      exact and_iff_right_of_imp (fun he => hsub (List.mem_toFinset.mpr he))
    _ = (ds.length : ℝ≥0∞) * ∫⁻ u, φ u ∂μ := by
      rw [Finset.sum_const, nsmul_eq_mul, List.toFinset_card_of_nodup hn,
        trace_edge_length]
    _ ≤ (∫⁻ u, φ u ∂μ) * R := by
      rw [mul_comm]
      gcongr

/-- Scalar monotonicity holds for negative as well as positive a. -/
lemma exponential_increment_monotone (a : ℝ) :
    MonotoneOn (fun u => ENNReal.ofReal ((exp (a*u/2)-1)^2)) (Set.Ici 0) := by
  intro u hu v hv huv
  change 0 ≤ u at hu
  change 0 ≤ v at hv
  apply ENNReal.ofReal_le_ofReal
  rcases le_total 0 a with ha | ha
  · have he : exp (a*u/2) ≤ exp (a*v/2) := exp_le_exp.mpr (by nlinarith)
    have h1 : 1 ≤ exp (a*u/2) := one_le_exp_iff.mpr (by nlinarith)
    nlinarith
  · have he : exp (a*v/2) ≤ exp (a*u/2) := exp_le_exp.mpr (by nlinarith)
    have h1 : exp (a*u/2) ≤ 1 := exp_le_one_iff.mpr (by nlinarith)
    nlinarith

lemma gamma_lintegral_half_exp_increment_square_le {shape rate a : ℝ}
    (hs : 0 < shape) (hr : 0 < rate) (ha : |a| ≤ rate/4) :
    (∫⁻ u : ℝ, ENNReal.ofReal ((exp (a*u/2)-1)^2) ∂gammaMeasure shape rate) ≤
      ENNReal.ofReal ((8*(2 : ℝ)^shape/rate^2)*a^2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (gamma_integrable_half_exp_increment_square hs hr ha)
    (Filter.Eventually.of_forall (fun u => sq_nonneg (exp (a*u/2)-1)))]
  exact ENNReal.ofReal_le_ofReal (gamma_integral_half_exp_increment_square_le hs hr ha)

/-- Quadratic Gamma proxy, uniform in ambient edge-set cardinality. -/
theorem sum_upward_exponential {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate)
    (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e) (p q : Vertex) (R : ℕ)
    (hR : latticeDistance p q < R) (a : ℝ) (ha : |a| ≤ rate/4) :
    (∑ e ∈ localEdges p q R, ∫⁻ u, ENNReal.ofReal
      ((exp (a * upward w p q R e u / 2)-1)^2) ∂gammaMeasure shape rate) ≤
      ENNReal.ofReal ((8*(2 : ℝ)^shape/rate^2)*a^2) * R := by
  apply (sum_upward_transform (gammaMeasure shape rate)
    ((gamma_ae_pos shape rate).mono (fun _ hu => hu.le))
    w hw p q R hR _ (exponential_increment_monotone a) (by simp)).trans
  exact _root_.mul_le_mul_left (gamma_lintegral_half_exp_increment_square_le hs hr ha) _

/-- The summed exponential upward increments are bounded uniformly over every
nonnegative finite coordinate assignment. -/
theorem finite_upward_exponential_sum {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate)
    (p q : Vertex) (R : ℕ) (hR : latticeDistance p q < R)
    (v : Coordinates p q R) (hv : ∀ e, 0 ≤ v e) (a : ℝ) (ha : |a| ≤ rate/4) :
    (∑ e : ↥(localEdges p q R), ∫⁻ u, ENNReal.ofReal
      ((exp (a * max (finitePassageTime p q R (Function.update v e u) -
        finitePassageTime p q R v) 0 / 2)-1)^2) ∂gammaMeasure shape rate) ≤
      ENNReal.ofReal ((8*(2 : ℝ)^shape/rate^2)*a^2) * R := by
  classical
  have hb := sum_upward_exponential hs hr (extend p q R v) (extend_nonneg p q R v hv)
    p q R hR a ha
  rw [← Finset.sum_attach (localEdges p q R)] at hb
  simpa only [Finset.attach_eq_univ, finitePassageTime, extend_update, upward] using hb

end GammaFPP.FiniteLocal

end OAI
