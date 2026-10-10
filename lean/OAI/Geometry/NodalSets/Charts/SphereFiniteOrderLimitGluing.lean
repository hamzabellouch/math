import Mathlib.Topology.UniformSpace.UniformConvergence
import OAI.Geometry.NodalSets.Charts.SphereSmallChartPartition
import OAI.Geometry.NodalSets.Elliptic.PartialJetGerm

namespace OAI

namespace Yau.Target
open Manifold Yau.Analysis Yau.Geometry Set Metric Filter
open scoped Topology ContDiff
noncomputable section

theorem sphere_finite_order_limit_gluing (P : Finset Base) (r : ℝ) (n : ℕ)
    (hcover : ∀ x : Base, ∃ p ∈ P, ∃ z ∈ ball (0 : Yau.Jets.Coord) r,
      sphereChartCoordMap p z=x)
    (w : ℕ → Base → ℝ)
    (f : {p // p ∈ P} → Yau.Jets.Coord → ℝ)
    (hf : ∀ p, ContDiffOn ℝ n (f p) (ball 0 r))
    (ht : ∀ p, TendstoUniformlyOn (fun j ↦ w j ∘ sphereChartCoordMap p.val)
      (f p) atTop (closedBall 0 r)) :
    ∃ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) n v ∧
      TendstoUniformly w v atTop ∧
      ∀ p : {p // p ∈ P}, EqOn (v ∘ sphereChartCoordMap p.val) (f p) (ball 0 r) := by
  classical
  have hcov (x : Base) : ∃ p : {p // p ∈ P}, ∃ z ∈ ball (0 : Yau.Jets.Coord) r,
      sphereChartCoordMap p.val z=x := by
    obtain ⟨p,hp,z,hz,he⟩ := hcover x
    exact ⟨⟨p,hp⟩,z,hz,he⟩
  choose c z hz he using hcov
  let v : Base → ℝ := fun x ↦ f (c x) (z x)
  have hvpoint (x : Base) : Tendsto (fun j ↦ w j x) atTop (𝓝 (v x)) := by
    have h := (ht (c x)).tendsto_at (ball_subset_closedBall (hz x))
    simpa only [Function.comp_apply,he,v] using h
  have hvchart (p : {p // p ∈ P}) :
      EqOn (v ∘ sphereChartCoordMap p.val) (f p) (ball 0 r) := by
    intro y hy
    exact tendsto_nhds_unique (hvpoint _) ((ht p).tendsto_at (ball_subset_closedBall hy))
  have hvsmooth : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) n v := by
    intro x
    have hsource : x ∈ (extChartAt (𝓡 4) (c x).val).source := by
      have h := sphereChartCoordMap_source (c x).val (z x)
      rwa [he x] at h
    have hchart := contMDiffAt_extChartAt' (I := 𝓡 4) (n := (n : ℕ∞ω))
      (x := (c x).val) (x' := x) (by simpa only [extChartAt_source] using hsource)
    let coord : Base → Yau.Jets.Coord := fun y ↦
      seedCoordEquiv.symm ((extChartAt (𝓡 4) (c x).val) y)
    have hc : ContMDiffAt (𝓡 4) 𝓘(ℝ,Yau.Jets.Coord) n coord x :=
      seedCoordEquiv.symm.contDiff.contMDiff.contMDiffAt.comp x hchart
    have hcx : coord x=z x := by
      have hi : (extChartAt (𝓡 4) (c x).val)
          (sphereChartCoordMap (c x).val (z x)) = seedCoordEquiv (z x) :=
        (extChartAt (𝓡 4) (c x).val).right_inv (by rw [centeredSphereChart_target]; trivial)
      rw [he x] at hi
      change seedCoordEquiv.symm ((extChartAt (𝓡 4) (c x).val) x)=z x
      rw [hi,seedCoordEquiv.symm_apply_apply]
    have hh := ((hf (c x)).contDiffAt (isOpen_ball.mem_nhds (hz x)))
    rw [← hcx] at hh
    have hh' := hh.comp_contMDiffAt hc
    apply hh'.congr_of_eventuallyEq
    have hb : ∀ᶠ y in 𝓝 x, coord y ∈ ball (0 : Yau.Jets.Coord) r :=
      hc.continuousAt (isOpen_ball.mem_nhds (hcx ▸ hz x))
    filter_upwards [(isOpen_extChartAt_source (c x).val).mem_nhds hsource,hb] with y hy hby
    have h := hvchart (c x) hby
    simpa only [Function.comp_apply,coord,sphereChartCoordMap,seedCoordEquiv.apply_symm_apply,
      (extChartAt (𝓡 4) (c x).val).left_inv hy] using h
  refine ⟨v,hvsmooth,?_,hvchart⟩
  rw [Metric.tendstoUniformly_iff]
  intro eps heps
  have hh (p : {p // p ∈ P}) := Metric.tendstoUniformlyOn_iff.mp (ht p) eps heps
  filter_upwards [Filter.eventually_all.mpr hh] with j hj x
  have h := hj (c x) (z x) (ball_subset_closedBall (hz x))
  simpa only [Function.comp_apply,he,v] using h

end
end Yau.Target

end OAI
