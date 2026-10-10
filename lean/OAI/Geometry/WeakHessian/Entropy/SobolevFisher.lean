import Mathlib
import OAI.Geometry.WeakHessian.Calculus.NormalizedRoots
import OAI.Geometry.WeakHessian.LocalBounds.CostConvergence
import OAI.Geometry.WeakHessian.Entropy.EntropyLimits

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile12
noncomputable section
namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] in
lemma sqrt_gradient_energy_le_upper {v D : X → ℝ} (hv : Sobolev m v)
    (hD : IsLocalWeakUpperGradient m v D) (hD2 : MemLp D 2 m) :
    Real.sqrt (∫ x,(weakGradient m v x)^2 ∂m) ≤ ‖hD2.toLp D‖ := by
  have H : (∫ x,(weakGradient m v x)^2 ∂m) ≤ ∫ x,D x^2 ∂m := by
    apply integral_mono_ae ((memLp_two_iff_integrable_sq hv.2.2.aestronglyMeasurable).mp hv.2.2)
      ((memLp_two_iff_integrable_sq hD2.aestronglyMeasurable).mp hD2)
    filter_upwards [(weakGradient_isMinimal hv.2.1.2).2 D hD,weakGradient_nonneg (m := m) v] with x hx hn
    nlinarith
  rw [← norm_toLp_sq_eq_integral hD2] at H
  simpa only [Real.sqrt_sq (norm_nonneg _)] using Real.sqrt_le_sqrt H

variable [ProperSpace X] [SigmaFinite m]

theorem RCD.compact_sobolev_entropy_fisher {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfin : FiniteOnBoundedSets m)
    (w : X → ℝ) (hw : Sobolev m w) (hwm : Measurable w)
    {B : ℝ} (hB : 0 ≤ B) (hwn : ∀ᵐ x ∂m, 0 ≤ w x) (hwB : ∀ᵐ x ∂m, w x ≤ B)
    (μ ν : ProbabilityMeasure X) (hμ : (μ:Measure X) = squareDensityMeasure m w)
    (o : X) (R : ℝ≥0)
    (hsμ : (μ:Measure X) (Metric.closedBall o R)ᶜ = 0)
    (hsν : (ν:Measure X) (Metric.closedBall o R)ᶜ = 0)
    {C : ℝ≥0∞} (hCt : C ≠ ∞) (hdν : (ν:Measure X) ≤ C • m) :
    ∃ π : ProbabilityMeasure (Curve X), BoundedTracks (π:Measure (Curve X)) ∧
      IsOptimalCoupling (endpointCoupling (π:Measure (Curve X))) μ ν ∧
      entropyReal m (μ:Measure X)-entropyReal m (ν:Measure X)+K/2*planEnergy (π:Measure (Curve X)) ≤
        2*Real.sqrt (∫ x,(weakGradient m w x)^2 ∂m)*Real.sqrt (planEnergy (π:Measure (Curve X))) := by
  let : IsProbabilityMeasure (squareDensityMeasure m w) := hμ ▸ inferInstance
  have hsw : ∀ᵐ x ∂squareDensityMeasure m w, x ∈ Metric.closedBall o R := by rw [← hμ]; exact ae_iff.mpr hsμ
  obtain ⟨vs,hLip,hvb,hvsupp,hvs,hvp,Ds,hDs,hUG,hV,hD⟩ :=
    hrcd.1.normalized_compact_root_approximation hfin hw hwm hB hwn hwB o R (squareDensity_zero_outside hwm hsw)
  let Q : ℝ≥0 := R+2
  let D : ℝ≥0∞ := C+ENNReal.ofReal ((2*B)^2)+1
  have hDt : D ≠ ∞ := ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hCt,ENNReal.ofReal_ne_top⟩,ENNReal.one_ne_top⟩
  have hD0 : D ≠ 0 := by dsimp [D]; positivity
  have hCD : C ≤ D := le_trans le_self_add le_self_add
  have hBD : ENNReal.ofReal ((2*B)^2) ≤ D := le_trans le_add_self le_self_add
  have hBsmall : ENNReal.ofReal (B^2) ≤ D :=
    (ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg B])).trans hBD
  have hdμ : (μ:Measure X) ≤ D • m := by
    rw [hμ]; exact dominated_mono_constant (squareDensity_le_of_bound hB hwn hwB) hBsmall
  have hdνD := dominated_mono_constant hdν hCD
  have hsμQ : ∀ᵐ x ∂(μ:Measure X), x ∈ Metric.closedBall o Q :=
    (ae_iff.mpr hsμ).mono fun x hx => (Metric.closedBall_subset_closedBall (by simp [Q] : (R:ℝ) ≤ (Q:ℝ))) hx
  have hsνQ : ∀ᵐ x ∂(ν:Measure X), x ∈ Metric.closedBall o Q :=
    (ae_iff.mpr hsν).mono fun x hx => (Metric.closedBall_subset_closedBall (by simp [Q] : (R:ℝ) ≤ (Q:ℝ))) hx
  let μs (n : ℕ) : ProbabilityMeasure X := squareDensityProbability m (vs n) (hvp n)
  have hms (n : ℕ) : (μs n:Measure X) = squareDensityMeasure m (vs n) := rfl
  have hds (n : ℕ) : (μs n:Measure X) ≤ D • m := by
    exact dominated_mono_constant (squareDensity_le_of_bound (by positivity : 0 ≤ 2*B)
      (ae_of_all _ fun x => (hvb n x).1) (ae_of_all _ fun x => (hvb n x).2)) hBD
  have hss (n : ℕ) : ∀ᵐ x ∂(μs n:Measure X), x ∈ Metric.closedBall o Q := by
    apply squareDensity_ae_support (vs n).continuous.measurable
    apply ae_of_all
    intro x hx
    have H : x ∉ tsupport (vs n) := fun h => hx (by simpa only [Q,NNReal.coe_add,NNReal.coe_ofNat] using hvsupp n h)
    exact image_eq_zero_of_notMem_tsupport H
  obtain ⟨π,hπ,hb,hgeo,hopt,hE,hchord,hcomp⟩ :=
    hrcd.1.exists_entropy_testPlan hN hfin μ ν o Q (ae_iff.mp hsμQ) (ae_iff.mp hsνQ) hD0 hDt hdμ hdνD
  have hex (n : ℕ) := hrcd.bounded_entropy_subdifferential hN hfin (vs n) (hLip n).choose_spec
    (fun x => (hvb n x).1) (μs n) ν (hms n) o Q (ae_iff.mp (hss n)) (ae_iff.mp hsνQ) hD0 hDt (hds n) hdνD
  choose ps φ ψ hps hbps hgps hops hφ hψ hdual hcontact hent using hex
  have hFisher (n : ℕ) : entropyReal m (μs n:Measure X) ≤
      entropyReal m (ν:Measure X)+2*‖(hDs n).toLp (Ds n)‖*Real.sqrt (planEnergy (ps n:Measure (Curve X)))-
        K/2*planEnergy (ps n:Measure (Curve X)) := by
    have hvS := squareDensity_sobolev_of_supported hfin (hLip n).choose_spec o Q (hss n)
    have H := (hps n).contact_gamma_fisher_bound hfin (hrcd.1.global_localGradientParallelogram hfin o hrcd.2)
      (hbps n) hvS (vs n).continuous.measurable (fun x => (hvb n x).1) (hφ n) (hdual n) (hcontact n)
      ((hops n).1.interpolation_endpoints.1.trans (hms n))
    have J := sqrt_gradient_energy_le_upper hvS (hUG n) (hDs n)
    have U := mul_le_mul_of_nonneg_right J (Real.sqrt_nonneg (planEnergy (ps n:Measure (Curve X))))
    linarith [hent n]
  have hcost : Tendsto (fun n => planEnergy (ps n:Measure (Curve X))) atTop (𝓝 (planEnergy (π:Measure (Curve X)))) := by
    apply optimal_energy_squareDensity_tendsto (fun n => (vs n).continuous.measurable) hwm hvs hw.1 hvp hV o Q hss
      (by rw [← hμ]; exact hsμQ) hsνQ ps π hbps hb (fun n => hops n)
    simpa only [← hμ] using hopt
  have hnorm := hD.norm
  have ha := ((tendsto_const_nhds (x := entropyReal m (ν:Measure X))).add
    ((hnorm.const_mul 2).mul (Real.continuous_sqrt.tendsto _ |>.comp hcost))).sub (hcost.const_mul (K/2))
  have hμlim : Tendsto μs atTop (𝓝 μ) := by
    have H := squareDensity_tendsto_probability (fun n => (vs n).continuous.measurable) hwm hvs hw.1 hvp inferInstance hV
    have he : squareDensityProbability m w inferInstance = μ := by apply Subtype.ext; exact hμ.symm
    rwa [he] at H
  have H := entropyReal_le_of_tendsto_supported hfin μs μ hμlim o Q hss hsμQ hDt hds hdμ ha hFisher
  have hn := Real.sqrt_sq (norm_nonneg (hw.2.2.toLp (weakGradient m w)))
  rw [norm_toLp_sq_eq_integral hw.2.2] at hn
  refine ⟨π,hb,hopt,?_⟩
  rw [← hn] at H
  linarith
end WeakHessian

end
end InlinedFile12

end OAI
