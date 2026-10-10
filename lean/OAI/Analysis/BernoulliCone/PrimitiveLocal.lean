import OAI.Analysis.BernoulliCone.VerticalGraphLocalization

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace MeasureTheory
open scoped Topology ContDiff NNReal
namespace Bernoulli.DeSilvaJerison
open Foliation

lemma above_U_isOpen : IsOpen {p:Space 7×ℝ|U p.1<p.2}:=
  isOpen_lt (U_continuous.comp continuous_fst) continuous_snd

lemma capTube_isOpen : IsOpen {p:Space 7×ℝ|U p.1<p.2 ∧
    Cylindrical.radiusSq axis ((upperParameter p.1 p.2)⁻¹ • p.1)<1} := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  have hq:ContinuousAt (fun z:Space 7×ℝ=>
      Cylindrical.radiusSq axis ((upperParameter z.1 z.2)⁻¹ • z.1)) p:=
    (Cylindrical.radiusSq_contDiff axis (n:=1)).continuous.continuousAt.comp
      (((upperParameter_continuousAt hp.1).inv₀ (upperParameter_spec hp.1).1.ne').smul continuous_fst.continuousAt)
  exact inter_mem (above_U_isOpen.mem_nhds hp.1) (hq.eventually (gt_mem_nhds hp.2))

lemma upperFlux_primitive_axis_lipschitz {u v:Space 7→ℝ}
    (hu:LocallyLipschitz u) (hv:LocallyLipschitz v) (huv:∀y,u y≤v y)
    (huU:∀y,U y<u y) {x:Space 7} (hqx:Cylindrical.radiusSq axis x=0) :
    ∃K:ℝ≥0,∃V∈𝓝 x,LipschitzOnWith K (verticalPotential upperFlux u v) V := by
  apply verticalPotential_smooth_germ hu hv huv capTube_isOpen
    (fun p hp=>(upperFlux_contDiffAt hp.1 hp.2.ne).of_le (by simp) |>.contDiffWithinAt)
    _ upperFlux_intervalIntegrable
  intro p hp
  have hpx:p.1=x:=hp.1
  change U p.1<p.2 ∧ Cylindrical.radiusSq axis ((upperParameter p.1 p.2)⁻¹ • p.1)<1
  rw [hpx]
  refine ⟨(huU x).trans_le hp.2.1,?_⟩
  rw [Cylindrical.radiusSq_smul,hqx,mul_zero]
  norm_num

lemma seamHeight_smooth_germ {x:Space 7} (hqx:0<Cylindrical.radiusSq axis x) :
    ∃σ:Space 7→ℝ,ContDiff ℝ 1 σ ∧ σ =ᶠ[𝓝 x] seamHeight := by
  have hD:IsOpen {y:Space 7|0<Cylindrical.radiusSq axis y}:=
    isOpen_lt continuous_const (Cylindrical.radiusSq_contDiff axis (n:=1)).continuous
  obtain ⟨σ,hσ,hσe⟩:=LocalExtension.exists_contDiff_extension (n:=1)
    (isCompact_singleton (x:=x)) hD (singleton_subset_iff.mpr hqx)
    (fun y hy=>(seamHeight_contDiffAt hy).of_le (by simp) |>.contDiffWithinAt)
  exact ⟨σ,hσ,by simpa using hσe⟩

lemma upperFlux_compact_tube {x:Space 7} {a b:ℝ} (hua:U x<a)
    (hqx:0<Cylindrical.radiusSq axis x) :
    ∃K:Set (Space 7×ℝ),IsCompact K ∧ ({x}×ˢ Icc a b)⊆interior K ∧
      (∀p∈K,U p.1<p.2) ∧ (∀p∈K,0<Cylindrical.radiusSq axis p.1) := by
  let D:Set (Space 7×ℝ):={p|U p.1<p.2 ∧ 0<Cylindrical.radiusSq axis p.1}
  have hD:IsOpen D:=above_U_isOpen.inter (isOpen_lt continuous_const
    ((Cylindrical.radiusSq_contDiff axis (n:=1)).continuous.comp continuous_fst))
  have hk:({x}×ˢ Icc a b)⊆D:=by
    intro p hp
    have hpx:p.1=x:=hp.1
    exact ⟨by rw [hpx]; exact hua.trans_le hp.2.1,by rwa [hpx]⟩
  obtain ⟨K,hK,hKi,hKD⟩:=exists_compact_between (isCompact_singleton.prod isCompact_Icc) hD hk
  exact ⟨K,hK,hKi,fun p hp=>(hKD hp).1,fun p hp=>(hKD hp).2⟩

lemma upperFlux_primitive_offaxis_lipschitz {u v:Space 7→ℝ}
    (hu:LocallyLipschitz u) (hv:LocallyLipschitz v) (huv:∀y,u y≤v y)
    (huU:∀y,U y<u y) {x:Space 7} (hqx:0<Cylindrical.radiusSq axis x) :
    ∃K:ℝ≥0,∃V∈𝓝 x,LipschitzOnWith K (verticalPotential upperFlux u v) V := by
  obtain ⟨K,hK,hKi,hKp,hKq⟩:=upperFlux_compact_tube (b:=v x) (huU x) hqx
  obtain ⟨A,B,hA,hB,hAe,hBe⟩:=compact_branch_extensions hK hKp hKq
  obtain ⟨σ,hσ,hσe⟩:=seamHeight_smooth_germ hqx
  have hn:=eventually_vertical_segment hu.continuous.continuousAt hv.continuous.continuousAt
    (huv x) (subset_interior_iff_mem_nhdsSet.mp hKi)
  apply locallyLipschitz_germ (clamped_split_locallyLipschitz hA hB hu hv hσ.locallyLipschitz)
  filter_upwards [hn,hσe] with y hy hye
  apply clamped_integral_identity hA.continuous hB.continuous (huv y) (upperFlux_intervalIntegrable y)
  · intro t ht hts
    have hp:(y,t)∈K:=hy (huv y) t ⟨ht.1.le,ht.2.le⟩
    rw [hAe hp,upperFlux_eq_exterior (hKp _ hp) (hKq _ hp) (by rwa [←hye])]
  · intro t ht hst
    have hp:(y,t)∈K:=hy (huv y) t ⟨ht.1.le,ht.2.le⟩
    exact (hBe _ hp (by rw [←hye]; exact hst.le)).symm

/-- The actual discontinuous calibration has a locally Lipschitz vertical
primitive whenever its endpoints stay strictly above U. This includes the
axis and the vertex, not just the smooth off-interface regions. -/
theorem upperFlux_primitive_locallyLipschitz {u v:Space 7→ℝ}
    (hu:LocallyLipschitz u) (hv:LocallyLipschitz v) (huv:∀y,u y≤v y)
    (huU:∀y,U y<u y) : LocallyLipschitz (verticalPotential upperFlux u v) := by
  intro x
  rcases (Cylindrical.radiusSq_nonneg axis x axis_norm).eq_or_lt with he|hl
  · exact upperFlux_primitive_axis_lipschitz hu hv huv huU he.symm
  · exact upperFlux_primitive_offaxis_lipschitz hu hv huv huU hl
end Bernoulli.DeSilvaJerison

end
end

end OAI
