import OAI.Geometry.RCD.Transport.TransportCostEnergy

namespace OAI

/-! # Mean variation along a fixed compressed transport plan -/

open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem SobolevSpace.plan_mean_energy (μ : Measure X) [μ.Regular]
    (hQ : QuadraticCheegerEnergy μ) (w : SobolevSpace μ hQ)
    (P : ProbabilityMeasure C(Time,X))
    (hgeo : ∀ᵐ γ ∂(P : Measure C(Time,X)), IsGeodesic γ)
    {C : ℝ≥0∞} (hC : C≠⊤)
    (hcomp : ∀ t : Time, (P : Measure C(Time,X)).map (fun γ => γ t)≤C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 (P : Measure C(Time,X)))
    {Ω : Set X} (hstay : ∀ t : Time, ∀ᵐ x ∂(P : Measure C(Time,X)).map (fun γ => γ t), x∈Ω) :
    ((∫ γ : C(Time,X), SobolevSpace.toLp μ hQ w (γ 1) ∂(P : Measure C(Time,X)))-
      (∫ γ : C(Time,X), SobolevSpace.toLp μ hQ w (γ 0) ∂(P : Measure C(Time,X))))^2≤
      (∫ γ : C(Time,X), dist (γ 0) (γ 1)^2 ∂(P : Measure C(Time,X)))*
        (C.toReal*∫ x in Ω, localGamma μ hQ w w x ∂μ) := by
  let u := SobolevSpace.toLp μ hQ w
  have hu (t : Time) : MemLp (fun γ : C(Time,X) => u (γ t)) 2 (P : Measure C(Time,X)) :=
    compressionPullback_memLp μ (P : Measure C(Time,X)) _ (measurable_path_eval t) hC (hcomp t) u
  have hh := norm_integral_le_integral_norm (μ := (P : Measure C(Time,X)))
    (fun γ : C(Time,X) => u (γ 1)-u (γ 0))
  rw [integral_sub ((hu 1).integrable (by norm_num)) ((hu 0).integrable (by norm_num)),
    Real.norm_eq_abs] at hh
  have hs := pow_le_pow_left₀ (abs_nonneg _) hh 2
  simp only [Real.norm_eq_abs,sq_abs] at hs
  have hb := (SobolevSpace.minimalSlope_isRelaxed μ hQ w).testPlan_cost_energy μ
    (P : Measure C(Time,X)) hgeo hC hcomp hD hstay
  have he : (∫ x in Ω, (SobolevSpace.minimalSlope μ hQ w x)^2 ∂μ)=
      ∫ x in Ω, localGamma μ hQ w w x ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (localGamma_self μ hQ w)] with x hx
    exact hx.symm
  rw [he] at hb
  exact hs.trans hb

end RegularPointCoordinates

end

end OAI
