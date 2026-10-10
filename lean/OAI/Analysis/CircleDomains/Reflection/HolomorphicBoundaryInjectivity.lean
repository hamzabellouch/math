import OAI.Analysis.CircleDomains.Reflection.SchwarzReflectionInjective
import Mathlib.Analysis.Complex.ReImTopology

namespace OAI

/-! For an open holomorphic map preserving the strict upper side, interior
injectivity forces injectivity also on the real boundary. Thus boundary
injectivity need not be supplied as an extra extension assumption. -/
open Set Function Filter Metric Complex
open scoped Topology ComplexConjugate
noncomputable section
namespace CircleDomainRigidity

lemma not_eventually_constant_at_real_boundary {U : Set ℂ} {F : ℂ → ℂ}
    (hU : IsOpen U) (hp : ∀z∈U,0<z.im → 0<(F z).im)
    {x : ℂ} (hx : x∈U) (hx0 : x.im=0) (hFx0 : (F x).im=0) :
    ¬ ∀ᶠz in 𝓝 x,F z=F x := by
  intro he
  have hxcl : x∈closure {z:ℂ | 0<z.im} := by
    rw [closure_setOfPred_lt_im]
    exact hx0.ge
  have : NeBot (𝓝[{z:ℂ | 0<z.im}] x) := mem_closure_iff_nhdsWithin_neBot.mp hxcl
  have hf : ∀ᶠz in 𝓝[{z:ℂ | 0<z.im}] x,False := by
    filter_upwards [he.filter_mono nhdsWithin_le_nhds,
      mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hx),self_mem_nhdsWithin] with z hz hzU hzpos
    have hh := hp z hzU hzpos
    rw [hz,hFx0] at hh
    exact lt_irrefl _ hh
  obtain ⟨z,hz⟩ := hf.exists
  exact hz

lemma holomorphic_map_nhds_at_real_boundary {U : Set ℂ} {F : ℂ → ℂ}
    (hU : IsOpen U) (hd : DifferentiableOn ℂ F U)
    (hp : ∀z∈U,0<z.im → 0<(F z).im)
    {x : ℂ} (hx : x∈U) (hx0 : x.im=0) (hFx0 : (F x).im=0) :
    map F (𝓝 x)=𝓝 (F x) := by
  apply le_antisymm
  · exact ((hd x hx).differentiableAt (hU.mem_nhds hx)).continuousAt
  · exact (hd.analyticAt (hU.mem_nhds hx)).eventually_constant_or_nhds_le_map_nhds.resolve_left
      (not_eventually_constant_at_real_boundary hU hp hx hx0 hFx0)

lemma holomorphic_injOn_upperClosed {U : Set ℂ} {F : ℂ → ℂ}
    (hU : IsOpen U) (hd : DifferentiableOn ℂ F U)
    (hp : ∀z∈U,0<(F z).im ↔ 0<z.im)
    (hr : ∀z∈U,z.im=0 → (F z).im=0)
    (hi : InjOn F (U∩{z:ℂ | 0<z.im})) :
    InjOn F (U∩{z:ℂ | 0≤z.im}) := by
  have hb : ∀x∈U,∀y∈U,x.im=0 → y.im=0 → F x=F y → x=y := by
    intro x hx y hy hx0 hy0 he
    by_contra hxy
    obtain ⟨A,B,hA,hB,hxA,hyB,hAB⟩ := t2_separation hxy
    have hxn := holomorphic_map_nhds_at_real_boundary hU hd (fun z hz => (hp z hz).mpr)
      hx hx0 (hr x hx hx0)
    have hyn := holomorphic_map_nhds_at_real_boundary hU hd (fun z hz => (hp z hz).mpr)
      hy hy0 (hr y hy hy0)
    have hAx : F '' (A∩U) ∈ 𝓝 (F x) := by
      rw [←hxn]
      exact image_mem_map ((hA.inter hU).mem_nhds ⟨hxA,hx⟩)
    have hBy : F '' (B∩U) ∈ 𝓝 (F x) := by
      rw [he,←hyn]
      exact image_mem_map ((hB.inter hU).mem_nhds ⟨hyB,hy⟩)
    have hxcl : F x∈closure {z:ℂ | 0<z.im} := by
      rw [closure_setOfPred_lt_im]
      exact (hr x hx hx0).ge
    have : NeBot (𝓝[{z:ℂ | 0<z.im}] (F x)) := mem_closure_iff_nhdsWithin_neBot.mp hxcl
    have hmeet : ∀ᶠz in 𝓝[{z:ℂ | 0<z.im}] (F x),
        z∈F '' (A∩U) ∧ z∈F '' (B∩U) ∧ 0<z.im := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds hAx,
        mem_nhdsWithin_of_mem_nhds hBy,self_mem_nhdsWithin] with z hzA hzB hzpos
      exact ⟨hzA,hzB,hzpos⟩
    obtain ⟨w,⟨a,ha,rfl⟩,⟨b,hb,hbe⟩,hwpos⟩ := hmeet.exists
    have hap : 0<a.im := (hp a ha.2).mp hwpos
    have hbp : 0<b.im := (hp b hb.2).mp (by rwa [hbe])
    have hab : a=b := hi ⟨ha.2,hap⟩ ⟨hb.2,hbp⟩ hbe.symm
    exact Set.disjoint_left.mp hAB ha.1 (hab.symm ▸ hb.1)
  intro x hx y hy he
  by_cases hxpos : 0<x.im
  · have hypos : 0<y.im := (hp y hy.1).mp (by rw [←he];exact (hp x hx.1).mpr hxpos)
    exact hi ⟨hx.1,hxpos⟩ ⟨hy.1,hypos⟩ he
  · have hx0 : x.im=0 := le_antisymm (le_of_not_gt hxpos) hx.2
    have hy0 : y.im=0 := by
      have hynp : ¬0<y.im := by
        intro h
        have hh := (hp y hy.1).mpr h
        rw [←he,hr x hx.1 hx0] at hh
        exact lt_irrefl _ hh
      exact le_antisymm (le_of_not_gt hynp) hy.2
    exact hb x hx.1 y hy.1 hx0 hy0 he

end CircleDomainRigidity

end

end OAI
