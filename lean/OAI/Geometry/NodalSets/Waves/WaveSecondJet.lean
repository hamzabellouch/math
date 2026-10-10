import OAI.Geometry.NodalSets.Charts.ContactGeometry
import OAI.Geometry.NodalSets.Coefficients.CoefficientLocality
import OAI.Geometry.NodalSets.Elliptic.CommonLocalExtension
import OAI.Geometry.NodalSets.Waves.WaveCenterJets

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {y : T → Coord} {d : SourceFrameTriple g S y} {m J K k0 : ℕ}
namespace TripleSourceWaveData
variable (b : TripleSourceWaveData g w S y d m J K k0)

omit [CompactSpace T] in
theorem phase_second
    (hg : ContDiff ℝ ∞ g) (hs : ∀ x u v, g x u v = g x v u)
    (hp : ∀ x v, v ≠ 0 → 0 < g x v v) (hS : ContDiff ℝ ∞ S)
    (hp0 : ∀ t, metricGradient g S (y t) ≠ 0) (t : T × Fin 3) (v : Coord) :
    sourceHessian g (fun z ↦ (b.phase t z).re) (y t.1) v v =
      sourceHessian g S (y t.1) v v -
        sourceDirectionEta (g (y t.1)) (sourceHessian g S (y t.1))
          (metricGradient g S (y t.1)) (d.q t.1 t.2) * g (y t.1) v v := by
  let f : Coord → ℝ := fun z ↦ (b.phase t z).re
  have hf : ContDiffOn ℝ ∞ f (b.F t).target := by
    intro z hz
    exact (Complex.reCLM.contDiff.contDiffAt.comp z
      ((reval_contDiff _).contDiffAt.comp z
        ((b.chart_domain t).2.2.contDiffAt ((b.F t).open_target.mem_nhds hz)))).contDiffWithinAt
  obtain ⟨r,A,hr,hA,_,_,_,_,hAe⟩ := common_local_smooth_extension
    (b.F t).open_target f hf (b.center_mem_target t)
  have hAf : A =ᶠ[𝓝 (y t.1)] f := hAe _ (Metric.mem_ball_self hr)
  let Q : Coord → Coord := actualMetricChart g (y t.1) (d.frame t)
  have hQ : ContDiff ℝ ∞ Q := quadraticChartMap_smooth _ _ _
  have hQ0 : Q 0 = y t.1 := quadraticChartMap_zero _ _ _
  have heF : (b.F t : Coord → Coord) = Q := b.chart_eq t
  have hAQ : (A ∘ Q) =ᶠ[𝓝 (0:Coord)] (fun z ↦ (reval (b.phi t) z).re) := by
    have hmap : Tendsto Q (𝓝 0) (𝓝 (y t.1)) := by simpa only [ContinuousAt,hQ0] using (hQ.continuous.continuousAt (x := 0))
    filter_upwards [hAf.comp_tendsto hmap,(b.F t).open_source.mem_nhds (b.zero_mem_source t)] with z hz hzs
    change A (Q z) = _
    change A (Q z) = f (Q z) at hz
    rw [hz]
    change (reval (b.phi t) ((b.F t).symm (Q z))).re = _
    rw [← heF,(b.F t).left_inv hzs]
  have hHess : sourceHessian g A (y t.1) = sourceHessian g f (y t.1) :=
    (sourceHessian_eventuallyEq (Filter.EventuallyEq.refl (𝓝 (y t.1)) g) hAf).self_of_nhds
  let a := sourceTripleAlpha g S y t
  let bb := sourceTripleBeta g S y t
  let H := envelopeHessian (S ∘ Q)
  have ha : a ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (hp (y t.1) (metricGradient g S (y t.1)) (hp0 t.1)))
  have hb : bb ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.mpr
    have hh := hp (y t.1) (metricGradient g S (y t.1)) (hp0 t.1)
    linarith
  have hSQ : ContDiff ℝ ∞ (S ∘ Q) := hS.comp hQ
  have hj := retained_normal_phase_derivatives (b.phi t) (S (y t.1)) a bb H ha hb
    (envelopeHessian_symmetric _ hSQ) (b.jets.phase_retained t)
  have heta : Yau.contactEta a bb (H 0 0) (H 1 1) =
      sourceDirectionEta (g (y t.1)) (sourceHessian g S (y t.1))
        (metricGradient g S (y t.1)) (d.q t.1 t.2) := by
    dsimp [H,Q]
    rw [charted_envelope_hessian g hg hs hp S hS,charted_envelope_hessian g hg hs hp S hS]
    exact source_eta_of_adapted_frame _ _ _ (d.frame_orthonormal t) _ _ a bb
      (d.frame_first (fun t ↦ hp (y t)) hp0 t) (d.frame_second (fun t ↦ hp (y t)) hp0 t)
  let u := (d.frame t).symm v
  have hsum : (∑ i, ∑ j, H i j*u i*u j) = sourceHessian g S (y t.1) v v := by
    rw [← envelopeHessian_diagonal]
    simpa only [u,Q,ContinuousLinearEquiv.apply_symm_apply] using
      scalar_chart_covariant_diagonal g hg hs hp S hS (y t.1) (d.frame t) u
  have hnorm : (∑ i, (u i)^2) = g (y t.1) v v := by
    simpa only [u,Q,ContinuousLinearEquiv.apply_symm_apply] using
      (orthonormal_frame_norm_sq (g (y t.1)) (d.frame t) (d.frame_orthonormal t) u).symm
  calc
    _ = sourceHessian g A (y t.1) v v := by rw [hHess]
    _ = iteratedFDeriv ℝ 2 (A ∘ Q) 0 (fun _ ↦ u) := by
      simpa only [u,Q,ContinuousLinearEquiv.apply_symm_apply] using
        (scalar_chart_covariant_diagonal g hg hs hp A hA (y t.1) (d.frame t) u).symm
    _ = iteratedFDeriv ℝ 2 (fun z ↦ (reval (b.phi t) z).re) 0 (fun _ ↦ u) := by
      rw [(hAQ.iteratedFDeriv ℝ 2).self_of_nhds]
    _ = (iteratedFDeriv ℝ 2 (reval (b.phi t)) 0 (fun _ ↦ u)).re := by
      exact congrArg (fun L : Coord [×2]→L[ℝ] ℝ ↦ L (fun _ ↦ u))
        (Complex.reCLM.iteratedFDeriv_comp_left (reval_contDiff _).contDiffAt
          (by change (↑(2:ℕ∞):ℕ∞ω) ≤ ↑(⊤:ℕ∞); exact WithTop.coe_le_coe.mpr le_top))
    _ = _ := by rw [hj.2.2 u,hsum,hnorm,heta]

end TripleSourceWaveData
end
end Yau.Geometry

end OAI
