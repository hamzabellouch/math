import OAI.Geometry.RCD.Transport.ContinuousDensityCoupling
import OAI.Geometry.RCD.Metric.LogDensitySlack
import OAI.Geometry.RCD.Transport.CompactCouplingSlack

namespace OAI

/-! # Equality-set concentration of normalized continuous kernels -/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
  [CompactSpace X] [CompactSpace Y] [SecondCountableTopology X] [SecondCountableTopology Y]
  (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

def continuousKernelLaw (H : C(X × Y,ℝ)) (hpos : ∀ z, 0 ≤ H z)
    (hrow : ∀ x, (∫ y, H (x,y) ∂ν)=1) : ProbabilityMeasure (X × Y) :=
  ⟨continuousDensityCoupling μ ν H,continuousDensityCoupling_probability μ ν H hpos hrow⟩

theorem continuous_kernel_saturation (H : ℕ → C(X × Y,ℝ))
    (hpos : ∀ k z, 0 < H k z)
    (hrow : ∀ k x, (∫ y, H k (x,y) ∂ν)=1)
    (hcol : ∀ k y, (∫ x, H k (x,y) ∂μ)=1)
    (ε : ℕ → ℝ) (hε : ∀ k, 0 ≤ ε k) (s : C(X × Y,ℝ))
    (hs : ∀ x y, y ∈ ν.support → s (x,y) ≤ 0)
    (hlog : TendstoUniformly (fun k z => ε k*Real.log (H k z)) s atTop) :
    ∃ (Q : ProbabilityMeasure (X × Y)) (ι : ℕ → ℕ), StrictMono ι ∧
      Tendsto (fun k => continuousKernelLaw μ ν (H (ι k))
        (fun z => (hpos (ι k) z).le) (hrow (ι k))) atTop (𝓝 Q) ∧
      (Q : Measure (X × Y)).map Prod.fst=μ ∧
      (Q : Measure (X × Y)).map Prod.snd=ν ∧
      ∀ᵐ z ∂(Q : Measure (X × Y)), s z=0 := by
  have hp (k : ℕ) := continuousDensityCoupling_probability μ ν (H k)
    (fun z => (hpos k z).le) (hrow k)
  let P : ℕ → ProbabilityMeasure (X × Y) := fun k =>
    continuousKernelLaw μ ν (H k) (fun z => (hpos k z).le) (hrow k)
  have hl (k : ℕ) : (P k : Measure (X × Y)).map Prod.fst=μ :=
    continuousDensityCoupling_fst μ ν (H k) (fun z => (hpos k z).le) (hrow k)
  have hr (k : ℕ) : (P k : Measure (X × Y)).map Prod.snd=ν :=
    continuousDensityCoupling_snd μ ν (H k) (fun z => (hpos k z).le) (hcol k)
  have hslack (k : ℕ) : ∀ᵐ z ∂(P k : Measure (X × Y)), s z ≤ 0 := by
    filter_upwards [coupling_snd_support (ν := ν) (π := (P k : Measure (X × Y))) (hr k)] with z hz
    exact hs z.1 z.2 hz
  have hlim := log_density_slack_integral (μ.prod ν) H hpos hp ε hε s hslack hlog
  exact compact_coupling_zero_slack μ ν P hl hr s hs hlim

end RegularPointCoordinates

end

end OAI
