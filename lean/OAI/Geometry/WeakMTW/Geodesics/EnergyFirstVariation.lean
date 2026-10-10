import Mathlib
import OAI.Geometry.WeakMTW.Variations.FirstVariation

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter CoordinateGeometry
open scoped Topology ContDiff
namespace FirstVariation
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

 theorem energy_pairing_hasDerivAt {G : E → MetricTensor E} {c V : ℝ × ℝ → E}
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hc : ContDiffOn ℝ 2 c U)
    (hct : ∀ z ∈ U, HasDerivAt (fun r => c (r,z.2)) (V z) z.1)
    {t : ℝ} (ht : (t,0) ∈ U) (hV : DifferentiableAt ℝ V (t,0))
    (hDG : DifferentiableAt ℝ G (c (t,0)))
    (hsym : ∀ v w, G (c (t,0)) v w = G (c (t,0)) w v)
    (hpos : ∀ v : E, v ≠ 0 → 0 < G (c (t,0)) v v)
    (hVt : HasDerivAt (fun r => V (r,0)) (-christoffel G (c (t,0)) (V (t,0)) (V (t,0))) t)
    {e : ℝ → ℝ} (he : (fun s => G (c (t,s)) (V (t,s)) (V (t,s))) =ᶠ[𝓝 (0 : ℝ)] e) :
    HasDerivAt (fun r => G (c (r,0)) (V (r,0)) (fderiv ℝ c (r,0) (0,1)))
      (deriv e 0 / 2) t := by
  have hcd := ((hc _ ht).contDiffAt (hU.mem_nhds ht)).differentiableAt (by norm_num)
  have hdJ := VariationCalculus.parameter_variation_hasDerivAt (w := (1 : ℝ)) hU hc hct ht hV
  have hpair := geodesic_pairing_hasDerivAt (G := G) (c := fun r => c (r,0)) (V := fun r => V (r,0)) (J := fun r => fderiv ℝ c (r,0) (0,1)) hDG hpos (hct _ ht) hVt hdJ
  have hde := hasDerivAt_metric_pairing hDG
    (parameter_hasDerivAt hcd) (parameter_hasDerivAt hV) (parameter_hasDerivAt hV)
  have hev := hde.deriv.symm.trans he.deriv_eq
  rw [hsym (fderiv ℝ V (t,0) (0,1)) (V (t,0))] at hev
  convert! hpair using 1
  linarith
end
end FirstVariation
end

end WeakMTWGlobalSupport

end OAI
