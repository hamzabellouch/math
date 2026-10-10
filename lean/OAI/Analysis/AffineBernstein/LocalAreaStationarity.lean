import Mathlib
import OAI.Analysis.AffineBernstein.LocalVelocity
import OAI.Analysis.AffineBernstein.ParametricChoiceTransport

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

/- Literal affine area is stationary for every compact smooth local ambient
variation, with any continuous inward normalized conormal/transverse choices.
The equation on the original graph, not an ambient stationary axiom, is used. -/
theorem affineMaximal_local_parametric_area_stationary {n : ℕ}
    {Ω K : Set (Space n)} (hΩ : IsOpen Ω) (hK : IsCompact K)
    (φ : OpenPartialHomeomorph (Space n) (Space n))
    (hφ : ContDiffOn ℝ ∞ φ φ.source) (hψ : ContDiffOn ℝ ∞ φ.symm φ.target)
    (hKφ : K ⊆ φ.source) (hφΩ : φ.target ⊆ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    {V : Space n → Space n × ℝ} (hV : ContDiffOn ℝ ∞ V φ.source)
    (hVK : tsupport V ⊆ K)
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ)
    (ν : ℝ → Space n → (Space n × ℝ) →L[ℝ] ℝ) (ξ : ℝ → Space n → Space n × ℝ)
    (hν : ∀ t x, x ∈ φ.source → (ν t x).comp
      (fderiv ℝ (fun y => L (φ y,u (φ y))+v+t • V y) x) = 0)
    (hξ : ∀ t x, x ∈ φ.source → ν t x (ξ t x) = 1)
    (hc : ∀ x ∈ K, 0 < ν 0 x (L ((0 : Space n),1)))
    (hcont : ∀ x ∈ K, ContinuousAt (fun q : ℝ × Space n => ν q.1 q.2 (L ((0 : Space n),1))) (0,x)) :
    HasDerivAt (fun t : ℝ => ∫ x in K, parametricAreaDensity (graphAmbientBasis n)
      (fun y => L (φ y,u (φ y))+v+t • V y) (ν t x) (ξ t x) x) 0 0 := by
  obtain ⟨β,a,hβ,ha,hβK,haK,he,hstat⟩ := affineMaximal_local_chart_stationary
    hΩ hK φ hφ hψ hKφ hφΩ hu hp hm hV hVK L v
  have hKi : IsCompact (φ '' K) := hK.image_of_continuousOn (φ.continuousOn.mono hKφ)
  have hiΩ : φ '' K ⊆ Ω := by
    rintro _ ⟨x,hx,rfl⟩
    exact hφΩ (φ.map_source (hKφ hx))
  have hpos : ∀ᶠ t : ℝ in nhds 0, ∀ x ∈ K, 0 < ν t x (L ((0 : Space n),1)) := by
    apply eventually_uniform_compact_zero hK (P := fun q => 0 < ν q.1 q.2 (L ((0 : Space n),1)))
    intro x hx
    exact (hcont x hx).preimage_mem_nhds (Ioi_mem_nhds (hc x hx))
  apply hstat.congr_of_eventuallyEq
  filter_upwards [hpos,eventually_graphVariation_positive hΩ hKi hiΩ hu hβ.contDiffOn
    (fun k => (ha k).contDiffOn) hp] with t ht hreg
  apply setIntegral_congr_fun hK.measurableSet
  intro x hx
  have hg : (fun y => L (φ y,u (φ y))+v+t • V y) =ᶠ[nhds x]
      ((fun y => L (graphParamVariation u β a t y)+v) ∘ φ) := by
    filter_upwards [φ.open_source.mem_nhds (hKφ hx)] with y hy
    exact (he y hy t).symm
  change parametricAreaDensity (graphAmbientBasis n) _ (ν t x) (ξ t x) x = _
  rw [parametricAreaDensity_congr (graphAmbientBasis n) hg]
  exact coordinateAffineVariationArea_choices hΩ φ.open_source hu hβ ha L v hφ
    (by rintro _ ⟨y,hy,rfl⟩; exact hφΩ (φ.map_source hy)) (hKφ hx)
    (smooth_chart_jacobian_ne φ hφ hψ (hKφ hx)) t
    (hreg (φ x) (mem_image_of_mem φ hx)).1 (hreg (φ x) (mem_image_of_mem φ hx)).2.le
    (ν t x) (ξ t x) (by rw [← hg.fderiv_eq]; exact hν t x (hKφ hx))
    (hξ t x (hKφ hx)) (ht x hx)

end AffineBernstein
end

end OAI
