import OAI.Geometry.RCD.Transport.PlanMeanEnergy

namespace OAI

/-! # The scale-invariant mean-energy inequality for the actual plan -/

open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem SobolevSpace.normalized_plan_mean_energy (μ : Measure X) [μ.Regular]
    (hQ : QuadraticCheegerEnergy μ) (w : SobolevSpace μ hQ)
    (P : ProbabilityMeasure C(Time,X))
    (hgeo : ∀ᵐ γ ∂(P : Measure C(Time,X)), IsGeodesic γ)
    {r a : ℝ} (hr : 0<r) (ha : 0≤a) {V : ℝ≥0∞} (hV : 0<V.toReal)
    (hcomp : ∀ t : Time, (P : Measure C(Time,X)).map (fun γ => γ t)≤
      (ENNReal.ofReal a*V⁻¹) • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 (P : Measure C(Time,X)))
    {Ω : Set X} (hstay : ∀ t : Time, ∀ᵐ x ∂(P : Measure C(Time,X)).map (fun γ => γ t), x∈Ω) :
    ((∫ γ : C(Time,X), SobolevSpace.toLp μ hQ w (γ 1) ∂(P : Measure C(Time,X)))-
      (∫ γ : C(Time,X), SobolevSpace.toLp μ hQ w (γ 0) ∂(P : Measure C(Time,X))))^2≤
      (∫ γ : C(Time,X), (dist (γ 0) (γ 1)/r)^2 ∂(P : Measure C(Time,X)))*a*
        (r^2/V.toReal*(∫ x in Ω, localGamma μ hQ w w x ∂μ)) := by
  have hV0 : V≠0 := by
    intro hh
    simp only [hh,ENNReal.toReal_zero,lt_self_iff_false] at hV
  have hC : ENNReal.ofReal a*V⁻¹≠⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.inv_ne_top.mpr hV0)
  have hb := w.plan_mean_energy μ hQ P hgeo hC hcomp hD hstay
  have hcap : (ENNReal.ofReal a*V⁻¹).toReal=a/V.toReal := by
    rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal ha,ENNReal.toReal_inv,div_eq_mul_inv]
  rw [hcap] at hb
  convert hb using 1
  simp_rw [div_pow,integral_div]
  field_simp [hr.ne',hV.ne']

end RegularPointCoordinates

end

end OAI
