import OAI.Geometry.NodalSets.Charts.MetricFrameOps

namespace OAI

namespace Yau.Geometry
open Filter
open scoped Topology
noncomputable section
variable {E T : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace T]

lemma admissibility_eventually (g H : T → E →L[ℝ] E →L[ℝ] ℝ) (p : T → E) (x : T)
    (hg : ContinuousAt g x) (hH : ContinuousAt H x) (hp : ContinuousAt p x)
    (hpp : 0 < g x (p x) (p x)) (t : E) (hpt : g x (p x) t = 0)
    (htt : g x t t = 1)
    (hstrict : 0 < H x (p x) (p x) + (g x (p x) (p x)+4)*H x t t) :
    ∀ᶠ y in 𝓝 x, p y ≠ 0 ∧ ∃ u : E, g y (p y) u = 0 ∧ g y u u = 1 ∧
      0 < H y (p y) (p y) + (g y (p y) (p y)+4)*H y u u := by
  let a : T → ℝ := fun y ↦ g y (p y) (p y)
  have ha : ContinuousAt a x := (hg.clm_apply hp).clm_apply hp
  let z : T → E := fun y ↦ t - (g y (p y) t / a y) • p y
  have hz : ContinuousAt z x := continuousAt_const.sub
    ((((hg.clm_apply hp).clm_apply continuousAt_const).div ha hpp.ne').smul hp)
  have hz0 : z x = t := by simp [z,hpt]
  have hzz : 0 < g x (z x) (z x) := by rw [hz0,htt]; norm_num
  let u : T → E := fun y ↦ metricNormalize (g y) (z y)
  have hu : ContinuousAt u x := metricNormalize_continuousAt g z hg hz hzz
  have hu0 : u x = t := by dsimp [u]; rw [hz0]; exact metricNormalize_fixed _ _ htt
  have hs : ContinuousAt (fun y ↦ H y (p y) (p y) + (a y+4)*H y (u y) (u y)) x :=
    ((hH.clm_apply hp).clm_apply hp).add
      ((ha.add continuousAt_const).mul ((hH.clm_apply hu).clm_apply hu))
  have hsa : ∀ᶠ y in 𝓝 x, 0 < H y (p y) (p y) + (a y+4)*H y (u y) (u y) :=
    hs.preimage_mem_nhds (Ioi_mem_nhds (by simpa [hu0,a] using hstrict))
  have haa : ∀ᶠ y in 𝓝 x, 0 < a y := ha.preimage_mem_nhds (Ioi_mem_nhds hpp)
  have hza : ∀ᶠ y in 𝓝 x, 0 < g y (z y) (z y) :=
    ((hg.clm_apply hz).clm_apply hz).preimage_mem_nhds (Ioi_mem_nhds hzz)
  filter_upwards [haa,hza,hsa] with y hy hyz hys
  have hp0 : p y ≠ 0 := by intro he; simp [a,he] at hy
  refine ⟨hp0,u y,?_,metricNormalize_unit _ _ hyz,hys⟩
  apply metricNormalize_orthogonal
  change g y (p y) (t - (g y (p y) t / a y) • p y) = 0
  simp only [map_sub,map_smul,smul_eq_mul]
  change g y (p y) t - (g y (p y) t / a y) * a y = 0
  rw [div_mul_cancel₀ _ hy.ne',sub_self]

end
end Yau.Geometry

end OAI
