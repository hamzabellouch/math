import Mathlib
import OAI.Geometry.WeakHessian.Calculus.CompactCost

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile10
noncomputable section
namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [SecondCountableTopology X] [ProperSpace X] {m : Measure X}

lemma bounded_plan_potentials {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (o : X) (R : ℝ≥0) (hμ : ∀ᵐ x ∂μ, x ∈ Metric.closedBall o R)
    (hν : ∀ᵐ x ∂ν, x ∈ Metric.closedBall o R)
    {π : Measure (Curve X)} (ho : IsOptimalCoupling (endpointCoupling π) μ ν) :
    ∃ φ ψ : X → ℝ, LipschitzWith (2*R) φ ∧ LipschitzWith (2*R) ψ ∧
      (∀ x y, φ x+ψ y ≤ dist x y^2/2) ∧
      ∀ᵐ γ ∂π, φ (γ timeZero)+ψ (γ timeOne) = dist (γ timeZero) (γ timeOne)^2/2 := by
  obtain ⟨φ,ψ,hφ,hψ,hd,hc⟩ := WeakHessianTransport.bounded_support_kantorovich_potentials
    (isCompact_closedBall o R) (Metric.nonempty_closedBall.mpr R.coe_nonneg) μ ν hμ hν ho
    (R := 2*R) (by
      intro x hx y hy
      have H := dist_triangle x o y
      rw [dist_comm o y] at H
      change dist x o ≤ R at hx
      change dist y o ≤ R at hy
      push_cast
      linarith)
  refine ⟨φ,ψ,hφ,hψ,hd,?_⟩
  apply (ae_map_iff ((continuous_eval_const timeZero).prodMk (continuous_eval_const timeOne)).measurable.aemeasurable ?_).mp hc
  exact (isClosed_eq ((hφ.continuous.comp continuous_fst).add (hψ.continuous.comp continuous_snd))
    (((continuous_fst.dist continuous_snd).pow 2).div_const 2)).measurableSet

lemma optimal_energy_squareDensity_bound {f g : X → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hf2 : MemLp f 2 m) (hg2 : MemLp g 2 m)
    [IsProbabilityMeasure (squareDensityMeasure m f)] [IsProbabilityMeasure (squareDensityMeasure m g)]
    {ν : Measure X} [IsProbabilityMeasure ν] (o : X) (R : ℝ≥0)
    (hsf : ∀ᵐ x ∂squareDensityMeasure m f, x ∈ Metric.closedBall o R)
    (hsg : ∀ᵐ x ∂squareDensityMeasure m g, x ∈ Metric.closedBall o R)
    (hsν : ∀ᵐ x ∂ν, x ∈ Metric.closedBall o R)
    {π η : Measure (Curve X)} [IsProbabilityMeasure π] [IsProbabilityMeasure η]
    (hbπ : BoundedTracks π) (hbη : BoundedTracks η)
    (hoπ : IsOptimalCoupling (endpointCoupling π) (squareDensityMeasure m f) ν)
    (hoη : IsOptimalCoupling (endpointCoupling η) (squareDensityMeasure m g) ν) :
    |planEnergy π-planEnergy η| ≤ 4*(R:ℝ)^2*(∫ x,|f x^2-g x^2| ∂m) := by
  have aux {u v : X → ℝ} (hu : Measurable u) (hv : Measurable v)
      (hu2 : MemLp u 2 m) (hv2 : MemLp v 2 m)
      [IsProbabilityMeasure (squareDensityMeasure m u)] [IsProbabilityMeasure (squareDensityMeasure m v)]
      (hsu : ∀ᵐ x ∂squareDensityMeasure m u, x ∈ Metric.closedBall o R)
      (hsv : ∀ᵐ x ∂squareDensityMeasure m v, x ∈ Metric.closedBall o R)
      {p q : Measure (Curve X)} [IsProbabilityMeasure p] [IsProbabilityMeasure q]
      (hbp : BoundedTracks p) (hbq : BoundedTracks q)
      (hop : IsOptimalCoupling (endpointCoupling p) (squareDensityMeasure m u) ν)
      (hoq : IsOptimalCoupling (endpointCoupling q) (squareDensityMeasure m v) ν) :
      planEnergy p-planEnergy q ≤ 4*(R:ℝ)^2*(∫ x,|u x^2-v x^2| ∂m) := by
    obtain ⟨φ,ψ,hφ,hψ,hd,hc⟩ := bounded_plan_potentials o R hsu hsν hop
    obtain ⟨hp0,hp1⟩ := hop.1.interpolation_endpoints
    obtain ⟨hq0,hq1⟩ := hoq.1.interpolation_endpoints
    have H := planEnergy_le_of_contact hbp hbq hbp.integrable_length_sq hbq.integrable_length_sq
      hφ hψ hd hc (hp1.trans hq1.symm)
    rw [hp0,hq0] at H
    have J := squareDensity_pairing_bound_supported hu hv hu2 hv2 hφ o R hsu hsv
    push_cast at J
    nlinarith [le_abs_self ((∫ x,φ x ∂squareDensityMeasure m u)-(∫ x,φ x ∂squareDensityMeasure m v))]
  apply abs_le.mpr
  constructor
  · have H := aux hg hf hg2 hf2 hsg hsf hbη hbπ hoη hoπ
    simp only [abs_sub_comm (g _^2)] at H
    linarith
  · exact aux hf hg hf2 hg2 hsf hsg hbπ hbη hoπ hoη

lemma optimal_energy_squareDensity_tendsto {fs : ℕ → X → ℝ} {w : X → ℝ}
    (hfm : ∀ n, Measurable (fs n)) (hwm : Measurable w)
    (hfs : ∀ n, MemLp (fs n) 2 m) (hw : MemLp w 2 m)
    (hP : ∀ n, IsProbabilityMeasure (squareDensityMeasure m (fs n)))
    [IsProbabilityMeasure (squareDensityMeasure m w)]
    (hF : Tendsto (fun n => (hfs n).toLp (fs n)) atTop (𝓝 (hw.toLp w)))
    {ν : Measure X} [IsProbabilityMeasure ν] (o : X) (R : ℝ≥0)
    (hsf : ∀ n, ∀ᵐ x ∂squareDensityMeasure m (fs n), x ∈ Metric.closedBall o R)
    (hsw : ∀ᵐ x ∂squareDensityMeasure m w, x ∈ Metric.closedBall o R)
    (hsν : ∀ᵐ x ∂ν, x ∈ Metric.closedBall o R)
    (ps : ℕ → ProbabilityMeasure (Curve X)) (η : ProbabilityMeasure (Curve X))
    (hbps : ∀ n, BoundedTracks (ps n:Measure (Curve X))) (hbη : BoundedTracks (η:Measure (Curve X)))
    (hops : ∀ n, IsOptimalCoupling (endpointCoupling (ps n:Measure (Curve X))) (squareDensityMeasure m (fs n)) ν)
    (hoη : IsOptimalCoupling (endpointCoupling (η:Measure (Curve X))) (squareDensityMeasure m w) ν) :
    Tendsto (fun n => planEnergy (ps n:Measure (Curve X))) atTop (𝓝 (planEnergy (η:Measure (Curve X)))) := by
  have H := (squareDensity_L1_tendsto hfs hw hF).const_mul (4*(R:ℝ)^2)
  simp only [mul_zero] at H
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) _ H
  intro n
  let := hP n
  exact optimal_energy_squareDensity_bound (hfm n) hwm (hfs n) hw o R (hsf n) hsw hsν
    (hbps n) hbη (hops n) hoη
end WeakHessian

end
end InlinedFile10

end OAI
