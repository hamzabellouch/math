import Mathlib
import OAI.Analysis.AffineBernstein.IntegratedParametricStationarity
import OAI.Analysis.AffineBernstein.ParametricTransport

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

/- The stationarity functional in any smooth nonsingular injective coordinate
chart. The change of variables uses the literal Lebesgue Jacobian, and positivity
for the full parameter family is derived uniformly from the original Hessian. -/
theorem affineMaximal_coordinate_parametric_area_stationary {n : ℕ}
    {Ω K : Set (Space n)} (hΩ : IsOpen Ω) (hK : IsCompact K)
    {φ : Space n → Space n} (hφ : ∀ x ∈ K, ContDiffAt ℝ ∞ φ x)
    (hinj : InjOn φ K) (hφJ : ∀ x ∈ K, (parametricJacobian φ x).det ≠ 0)
    (hKΩ : φ '' K ⊆ Ω) {u β : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (hβ : ContDiff ℝ ∞ β) (hβK : tsupport β ⊆ φ '' K)
    {a : Fin n → Space n → ℝ} (ha : ∀ k, ContDiff ℝ ∞ (a k))
    (haK : ∀ k, tsupport (a k) ⊆ φ '' K)
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ) :
    HasDerivAt (fun t : ℝ => ∫ x in K, coordinateAffineVariationArea L v φ u β a x t) 0 0 := by
  have hKi : IsCompact (φ '' K) := hK.image_of_continuousOn
    (fun x hx => (hφ x hx).continuousAt.continuousWithinAt)
  have hstat := affineMaximal_affine_parametric_area_stationary hΩ hKi hKΩ hu hp hm
    hβ hβK ha haK L v
  apply hstat.congr_of_eventuallyEq
  filter_upwards [eventually_graphVariation_positive hΩ hKi hKΩ hu hβ.contDiffOn
    (fun k => (ha k).contDiffOn) hp] with t ht
  calc
    (∫ x in K, coordinateAffineVariationArea L v φ u β a x t) =
        ∫ x in K, |LinearMap.det (fderiv ℝ φ x).toLinearMap| *
          affineParametricVariationArea L v u β a (φ x) t := by
      apply setIntegral_congr_fun hK.measurableSet
      intro x hx
      have hh := ht (φ x) (mem_image_of_mem φ hx)
      exact coordinateAffineVariationArea_eq hΩ hu hβ.contDiffOn (fun k => (ha k).contDiffOn)
        L v (hφ x hx) (hKΩ (mem_image_of_mem φ hx)) (hφJ x hx) t hh.1 hh.2.le
    _ = ∫ x in φ '' K, affineParametricVariationArea L v u β a x t := by
      simpa only [smul_eq_mul] using
        (integral_image_eq_integral_abs_det_fderiv_smul volume hK.measurableSet
          (fun x hx => ((hφ x hx).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt)
          hinj (fun x => affineParametricVariationArea L v u β a x t)).symm

end AffineBernstein
end

end OAI
