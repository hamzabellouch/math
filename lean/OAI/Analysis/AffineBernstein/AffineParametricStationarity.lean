import Mathlib
import OAI.Analysis.AffineBernstein.ParametricStationarity
import OAI.Analysis.AffineBernstein.GraphParametricArea

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

/- The literal arbitrary affine image of a parametrized graph variation. -/
def affineParametricVariationArea {n : ℕ} (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ))
    (v : Space n × ℝ) (u β : Space n → ℝ) (a : Fin n → Space n → ℝ)
    (x : Space n) (t : ℝ) : ℝ :=
  parametricAreaDensity (graphAmbientBasis n)
    (fun y => L (graphParamVariation u β a t y) + v)
    ((graphParamConormal u β a x t).comp L.symm.toContinuousLinearMap)
    (L ((0 : Space n), 1)) x

lemma affineParametricVariationArea_eq {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u β : Space n → ℝ} {a : Fin n → Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hβ : ContDiffOn ℝ ∞ β Ω)
    (ha : ∀ k, ContDiffOn ℝ ∞ (a k) Ω)
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ)
    {x : Space n} (hx : x ∈ Ω) (t : ℝ) :
    affineParametricVariationArea L v u β a x t =
      Real.rpow |LinearMap.det L.toLinearEquiv.toLinearMap| ((n : ℝ) / ((n : ℝ) + 2)) *
        graphVariationArea u β a x t := by
  unfold affineParametricVariationArea
  rw [parametricAreaDensity_affine _ (differentiableAt_graphParamVariation
    ((hu.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp))
    ((hβ.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp))
    (fun k => ((ha k).contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)) t),
    parametricAreaDensity_graphVariation hΩ hu hβ ha hx]

/- Stationarity is genuinely preserved by every ambient affine transformation.
The integrand is the derivative of the actual transformed parametric density.
No equation for the affine image is assumed. -/
theorem affineMaximal_affine_parametric_first_variation {n : ℕ} {Ω K : Set (Space n)}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {u β : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (hβ : ContDiff ℝ ∞ β) (hβK : tsupport β ⊆ K)
    {a : Fin n → Space n → ℝ} (ha : ∀ k, ContDiff ℝ ∞ (a k))
    (haK : ∀ k, tsupport (a k) ⊆ K)
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ) :
    IntegrableOn (fun x => deriv (affineParametricVariationArea L v u β a x) 0) Ω ∧
      (∫ x in Ω, deriv (affineParametricVariationArea L v u β a x) 0) = 0 := by
  let c := Real.rpow |LinearMap.det L.toLinearEquiv.toLinearMap|
    ((n : ℝ) / ((n : ℝ) + 2))
  have h0 := affineMaximal_parametric_first_variation hΩ hK hKΩ hu hp hm hβ hβK ha haK
  have he (x : Space n) (hx : x ∈ Ω) :
      deriv (affineParametricVariationArea L v u β a x) 0 = c * deriv (graphVariationArea u β a x) 0 := by
    have hef : affineParametricVariationArea L v u β a x = fun t => c * graphVariationArea u β a x t :=
      funext (fun t => affineParametricVariationArea_eq hΩ hu hβ.contDiffOn
        (fun k => (ha k).contDiffOn) L v hx t)
    rw [hef, deriv_const_mul _ (hasDerivAt_graphVariationArea_raw a (hp x hx)).differentiableAt]
  have hi : IntegrableOn (fun x => c * deriv (graphVariationArea u β a x) 0) Ω := h0.1.const_mul c
  refine ⟨hi.congr_fun (fun x hx => (he x hx).symm) hΩ.measurableSet, ?_⟩
  rw [setIntegral_congr_fun hΩ.measurableSet he, integral_const_mul, h0.2, mul_zero]

end AffineBernstein
end

end OAI
