import OAI.Analysis.CircleDomains.Reflection.AnalyticJordanParametrization

namespace OAI

/-! Two distinct boundary points cannot have the same image when their
local open extensions approach the same target side and the original
interior map is injective. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma injOn_boundary_of_holomorphic_extensions {A K B : Set ℂ} {f F : ℂ → ℂ}
    (hi : InjOn f A) (hFK : MapsTo F K (closure B))
    (hl : ∀x∈K,∃(O:Set ℂ)(g:ℂ→ℂ),IsOpen O ∧ x∈O ∧
      DifferentiableOn ℂ g O ∧ InjOn g O ∧ g x=F x ∧ EqOn g f (O∩A) ∧
      ∀z∈O,g z∈B → z∈A) : InjOn F K := by
  intro x hx y hy he
  by_contra hxy
  obtain ⟨P,Q,hP,hQ,hxP,hyQ,hPQ⟩ := t2_separation hxy
  obtain ⟨O,g,hO,hxO,hgd,hgi,hgx,hgf,hgB⟩ := hl x hx
  obtain ⟨V,h,hV,hyV,hhd,hhi,hhy,hhf,hhB⟩ := hl y hy
  have hgn : g '' (O∩P) ∈ 𝓝 (F x) := by
    rw [←hgx,←holomorphicInjOn_map_nhds hO hgd hgi hxO]
    exact image_mem_map ((hO.inter hP).mem_nhds ⟨hxO,hxP⟩)
  have hhn : h '' (V∩Q) ∈ 𝓝 (F x) := by
    rw [he,←hhy,←holomorphicInjOn_map_nhds hV hhd hhi hyV]
    exact image_mem_map ((hV.inter hQ).mem_nhds ⟨hyV,hyQ⟩)
  have : NeBot (𝓝[B] (F x)) := mem_closure_iff_nhdsWithin_neBot.mp (hFK hx)
  have hmeet : ∀ᶠz in 𝓝[B] (F x),z∈g '' (O∩P) ∧ z∈h '' (V∩Q) ∧ z∈B := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds hgn,
      mem_nhdsWithin_of_mem_nhds hhn,self_mem_nhdsWithin] with z hzg hzh hzB
    exact ⟨hzg,hzh,hzB⟩
  obtain ⟨w,⟨u,hu,rfl⟩,⟨v,hv,hvu⟩,hwB⟩ := hmeet.exists
  have huA : u∈A := hgB u hu.1 hwB
  have hvA : v∈A := hhB v hv.1 (by rwa [hvu])
  have huv : u=v := hi huA hvA (by
    calc
      f u = g u := (hgf ⟨hu.1,huA⟩).symm
      _ = h v := hvu.symm
      _ = f v := hhf ⟨hv.1,hvA⟩)
  exact Set.disjoint_left.mp hPQ hu.2 (huv.symm ▸ hv.2)

end CircleDomainRigidity

end

end OAI
