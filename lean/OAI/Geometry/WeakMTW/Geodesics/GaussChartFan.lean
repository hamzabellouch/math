import Mathlib
import OAI.Geometry.WeakMTW.Geodesics.GlobalFirstVariation

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

 theorem fanMomentum_coord_deriv (x : M) {P : ℝ → TangentBundle (model n) M}
    (hP : ContMDiff 𝓘(ℝ, ℝ) ((model n).prod (model n)) ∞ P) {t : ℝ}
    (ht : (t,0) ∈ fanDomain x P) :
    fanMomentum P t = metric x (fanCoordinates x P (t,0)).1
      (fanCoordinates x P (t,0)).2
      (deriv (fun s => (fanCoordinates x P (t,s)).1) 0) := by
  have hq := ((fanCoordinates_smooth x hP _ ht).contDiffAt
    ((fanDomain_open x hP).mem_nhds ht)).differentiableAt (by simp)
  rw [(FirstVariation.parameter_hasDerivAt hq.fst).deriv]
  exact fanMomentum_coord x hP ht

 theorem gauss_chart_fan (x : M) {P : ℝ → TangentBundle (model n) M}
    (hP : ContMDiff 𝓘(ℝ, ℝ) ((model n).prod (model n)) ∞ P)
    (b : M) (hbase : ∀ s, (P s).1 = b) (t s : ℝ)
    (ht : geodesicFlow t (P s) ∈ (stateChart x).source) :
    metric x (stateChart x (geodesicFlow t (P s))).1 (stateChart x (geodesicFlow t (P s))).2
      (deriv (fun r => (stateChart x (geodesicFlow t (P r))).1) s) =
      t * (deriv (fun r => ‖(P r).2‖^2) s / 2) := by
  let Q : ℝ → TangentBundle (model n) M := fun r => P (r+s)
  have hQ : ContMDiff 𝓘(ℝ, ℝ) ((model n).prod (model n)) ∞ Q :=
    hP.comp (contMDiff_iff_contDiff.mpr (contDiff_id.add contDiff_const))
  have hQ₀ : fanMomentum Q 0 = 0 := by
    have he : (fun r => geodesic (Q r) 0) = fun _ : ℝ => b := by
      funext r
      exact (geodesic_zero _).trans (hbase _)
    have hderiv : mfderiv 𝓘(ℝ, ℝ) (model n) (fun r => geodesic (Q r) 0) 0 = 0 := by
      rw [he, mfderiv_const]
      rfl
    rw [fanMomentum, hderiv]
    change inner ℝ (geodesicFlow 0 (Q 0)).2 0 = 0
    exact inner_zero_right _
  have htQ : (t,0) ∈ fanDomain x Q := by
    simpa only [fanDomain,geodesicFan,Q,zero_add,mem_preimage] using ht
  have hm := fanMomentum_coord_deriv x hQ htQ
  have hh := fanMomentum_affine hQ t
  rw [hm,hQ₀,zero_add] at hh
  dsimp only [fanCoordinates,geodesicFan,Q] at hh
  rw [deriv_comp_add_const (fun r => (stateChart x (geodesicFlow t (P r))).1) s 0,
    deriv_comp_add_const (fun r => ‖(P r).2‖^2) s 0] at hh
  simpa only [zero_add] using hh

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
