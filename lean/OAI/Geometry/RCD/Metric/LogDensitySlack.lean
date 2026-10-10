import OAI.Geometry.RCD.Transport.ContinuousDensityEntropy
import OAI.Geometry.RCD.Sobolev.UniformRealAlgebra

namespace OAI

/-! # Vanishing mean slack for normalized positive densities -/

open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

theorem log_density_slack_integral (h : ℕ → C(X,ℝ)) (hpos : ∀ k x, 0 < h k x)
    (hp : ∀ k, IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (h k x))))
    (ε : ℕ → ℝ) (hε : ∀ k, 0 ≤ ε k) (s : C(X,ℝ))
    (hs : ∀ k, ∀ᵐ x ∂μ.withDensity (fun x => ENNReal.ofReal (h k x)), s x ≤ 0)
    (hlim : TendstoUniformly (fun k x => ε k*Real.log (h k x)) s atTop) :
    Tendsto (fun k => ∫ x, s x ∂μ.withDensity (fun x => ENNReal.ofReal (h k x)))
      atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro η hη
  filter_upwards [(Metric.tendstoUniformly_iff.mp hlim) (η/2) (half_pos hη)] with k hk
  let π := μ.withDensity (fun x => ENNReal.ofReal (h k x))
  let : IsProbabilityMeasure π := hp k
  have hi : Integrable s π := s.continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hl : Integrable (fun x => ε k*Real.log (h k x)) π :=
    (((h k).continuous.log (fun x => (hpos k x).ne')).const_mul (ε k)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hnonneg : 0 ≤ ∫ x, ε k*Real.log (h k x) ∂π := by
    rw [integral_const_mul]
    exact mul_nonneg (hε k) (continuous_density_entropy_nonneg μ (h k) (hpos k))
  have hle := integral_mono_ae hl (hi.add (integrable_const (η/2)))
    (Eventually.of_forall fun x => by
      have hx := hk x
      rw [Real.dist_eq] at hx
      rcases abs_lt.mp hx with ⟨hlo,hup⟩
      change ε k*Real.log (h k x) ≤ s x+η/2
      linarith)
  change (∫ x, ε k*Real.log (h k x) ∂π) ≤ (∫ x, s x+η/2 ∂π) at hle
  rw [integral_add hi (integrable_const (η/2)),integral_const] at hle
  have hn : (∫ x, s x ∂π) ≤ 0 := integral_nonpos_of_ae (hs k)
  change dist (∫ x, s x ∂π) 0 < η
  simp only [probReal_univ,smul_eq_mul,one_mul] at hle
  rw [Real.dist_eq,sub_zero,abs_of_nonpos hn]
  linarith

end RegularPointCoordinates

end

end OAI
