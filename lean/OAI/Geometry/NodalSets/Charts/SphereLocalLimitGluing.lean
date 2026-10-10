import OAI.Geometry.NodalSets.Charts.SupportedFiniteAtlasBounds

namespace OAI

namespace Yau.Target
open Manifold Filter Set Yau.Geometry
open scoped ContDiff Topology
noncomputable section
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem sphere_local_limit_gluing (P : Finset Base)
    (hcover : ∀ x : Base, ∃ p ∈ P, ∃ z ∈ interior sphereAtlasCore,
      (extChartAt (𝓡 4) p).symm z = x)
    (w : ℕ → Base → F)
    (hlim : ∀ p ∈ P, ∃ f : BaseModel → F,
      ContDiffOn ℝ ∞ f (interior sphereAtlasCore) ∧
      ∀ z ∈ interior sphereAtlasCore,
        Tendsto (fun n ↦ w n ((extChartAt (𝓡 4) p).symm z)) atTop (𝓝 (f z))) :
    ∃ v : Base → F, ContMDiff (𝓡 4) 𝓘(ℝ,F) ∞ v ∧
      ∀ x, Tendsto (fun n ↦ w n x) atTop (𝓝 (v x)) := by
  classical
  choose f hf ht using (fun p : P ↦ hlim p.val p.property)
  have hex (x : Base) : ∃ p : P, ∃ z ∈ interior sphereAtlasCore,
      (extChartAt (𝓡 4) p.val).symm z = x := by
    obtain ⟨p,hp,z,hz,he⟩ := hcover x
    exact ⟨⟨p,hp⟩,z,hz,he⟩
  choose c z hz he using hex
  let v : Base → F := fun x ↦ f (c x) (z x)
  have hv (x : Base) : Tendsto (fun n ↦ w n x) atTop (𝓝 (v x)) := by
    simpa only [he,v] using ht (c x) (z x) (hz x)
  have hvchart (p : P) (y : BaseModel) (hy : y ∈ interior sphereAtlasCore) :
      v ((extChartAt (𝓡 4) p.val).symm y) = f p y :=
    tendsto_nhds_unique (hv _) (ht p y hy)
  refine ⟨v,?_,hv⟩
  intro x
  have htarget : z x ∈ (extChartAt (𝓡 4) (c x).val).target := by
    rw [centeredSphereChart_target]; trivial
  have hsource : x ∈ (extChartAt (𝓡 4) (c x).val).source := by
    simpa only [he x] using (extChartAt (𝓡 4) (c x).val).map_target htarget
  have hcoord : (extChartAt (𝓡 4) (c x).val) x = z x := by
    simpa only [he x] using (extChartAt (𝓡 4) (c x).val).right_inv htarget
  have hchart := contMDiffAt_extChartAt' (I := 𝓡 4) (n := ∞)
    (x := (c x).val) (x' := x) (by simpa only [extChartAt_source] using hsource)
  have hlocal : ContDiffAt ℝ ∞ (f (c x)) ((extChartAt (𝓡 4) (c x).val) x) := by
    rw [hcoord]
    exact (hf (c x) (z x) (hz x)).contDiffAt (isOpen_interior.mem_nhds (hz x))
  apply (hlocal.contMDiffAt.comp x hchart).congr_of_eventuallyEq
  have hnear : ∀ᶠ y in 𝓝 x, (extChartAt (𝓡 4) (c x).val) y ∈ interior sphereAtlasCore :=
    hchart.continuousAt (by rw [hcoord]; exact isOpen_interior.mem_nhds (hz x))
  filter_upwards [hnear,(isOpen_extChartAt_source (c x).val).mem_nhds hsource] with y hy hs
  have h := hvchart (c x) ((extChartAt (𝓡 4) (c x).val) y) hy
  simpa only [(extChartAt (𝓡 4) (c x).val).left_inv hs,Function.comp_apply] using h

end
end Yau.Target

end OAI
