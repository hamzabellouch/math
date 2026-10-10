import Mathlib
import OAI.Geometry.WeakMTW.Coordinates.CoordinateEquation
import OAI.Geometry.WeakMTW.Variations.SecondCurveChain

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem chart_geodesic_second (x : M) (ξ : TangentSpace (model n) x)
    (f : Model n → ℝ) (hf : ContDiffAt ℝ 2 f (chartAt (Model n) x x)) :
    deriv (deriv (fun t : ℝ => f (chartAt (Model n) x (exp x (t • ξ))))) 0 =
      fderiv ℝ (fderiv ℝ f) (chartAt (Model n) x x)
        (stateChart x (⟨x,ξ⟩ : TangentBundle (model n) M)).2
        (stateChart x (⟨x,ξ⟩ : TangentBundle (model n) M)).2 -
      fderiv ℝ f (chartAt (Model n) x x)
        (christoffel (metric x) (chartAt (Model n) x x)
          (stateChart x (⟨x,ξ⟩ : TangentBundle (model n) M)).2
          (stateChart x (⟨x,ξ⟩ : TangentBundle (model n) M)).2) := by
  let p : TangentBundle (model n) M := ⟨x,ξ⟩
  let C : ℝ → Model n := fun t => chartAt (Model n) x (geodesic p t)
  let V : ℝ → Model n := fun t => (stateChart x (geodesicFlow t p)).2
  let a := chartAt (Model n) x x
  let u := (stateChart x p).2
  have hx : x ∈ (chartAt (Model n) x).source := mem_chart_source (Model n) x
  have hC₀ : C 0 = a := by simp [C,a,p,geodesic_zero]
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, geodesic p t ∈ (chartAt (Model n) x).source := by
    have hp : geodesic p 0 ∈ (chartAt (Model n) x).source := by simpa only [geodesic_zero, p] using hx
    exact (geodesic_smooth p).continuous.continuousAt.preimage_mem_nhds
      ((chartAt (Model n) x).open_source.mem_nhds hp)
  have hcd : ∀ᶠ t : ℝ in 𝓝 0, HasDerivAt C (V t) t := by
    filter_upwards [hnear] with t ht
    exact (geodesic_coordinate_equation x p t ht).fst
  have hV₀ : V 0 = u := by simp only [V,u,geodesicFlow_zero]
  have hdc : HasDerivAt C u 0 := hV₀ ▸ hcd.self_of_nhds
  have hstate := geodesic_coordinate_equation_zero x p hx
  have hVd : HasDerivAt V (-christoffel (metric x) a u u) 0 := hstate.snd
  have hdeq : deriv C =ᶠ[𝓝 (0 : ℝ)] V := hcd.mono (fun _ ht => ht.deriv)
  have hdd : HasDerivAt (deriv C) (-christoffel (metric x) a u u) 0 :=
    hVd.congr_of_eventuallyEq hdeq
  have hcS : ContDiffAt ℝ ∞ C 0 := by
    apply contMDiffAt_iff_contDiffAt.mp
    have hh : ContMDiffAt (model n) (model n) ∞ (chartAt (Model n) x) x := contMDiffOn_chart.contMDiffAt
      ((chartAt (Model n) x).open_source.mem_nhds hx)
    have hc := (geodesic_smooth p).contMDiffAt (x := (0 : ℝ))
    have hcx : geodesic p 0 = x := by simp only [geodesic_zero,p]
    have hh' : ContMDiffAt (model n) (model n) ∞ (chartAt (Model n) x) (geodesic p 0) := by
      rw [hcx]
      exact hh
    exact hh'.comp 0 hc
  have hfC : ContDiffAt ℝ 2 f (C 0) := by rw [hC₀]; exact hf
  have hh := SecondCurveChain.second hfC (hcS.of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)) hdc hdd
  simp only [hC₀,map_neg,← sub_eq_add_neg] at hh
  have he : (fun t : ℝ => f (chartAt (Model n) x (exp x (t • ξ)))) = f ∘ C := by
    ext t
    rw [exp_mul_eq_geodesic (p := p)]
    rfl
  rw [he]
  exact hh

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
