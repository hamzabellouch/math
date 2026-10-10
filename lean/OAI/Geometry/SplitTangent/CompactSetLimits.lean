import Mathlib

namespace OAI

/-! Compact Set Limits. -/

noncomputable section
open Set Filter Topology TopologicalSpace
universe u v
namespace CompactSetLimits
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

lemma isOpen_exists_mem {W : Set (Y × X)} (hW : IsOpen W) :
    IsOpen {p : Y × Compacts X | ∃x∈(p.2 : Set X),(p.1,x)∈W} := by
  apply isOpen_iff_mem_nhds.mpr
  rintro ⟨y,K⟩ ⟨x,hx,hxy⟩
  obtain ⟨U,V,hU,hV,hy,hxV,hUV⟩ := isOpen_prod_iff.mp hW y x hxy
  have hN : U ×ˢ {L : Compacts X | ((L : Set X)∩V).Nonempty} ∈ 𝓝 (y,K) :=
    (hU.prod (Compacts.isOpen_inter_nonempty_of_isOpen hV)).mem_nhds ⟨hy,x,hx,hxV⟩
  apply mem_of_superset hN
  rintro ⟨z,L⟩ ⟨hz,w,hw,hwV⟩
  exact ⟨w,hw,hUV ⟨hz,hwV⟩⟩

lemma isClosed_forall_mem {C : Set (Y × X)} (hC : IsClosed C) :
    IsClosed {p : Y × Compacts X | ∀x∈(p.2 : Set X),(p.1,x)∈C} := by
  have hh := (isOpen_exists_mem hC.isOpen_compl).isClosed_compl
  convert hh using 1
  ext p
  simp

lemma isClosed_incidence [T2Space X] :
    IsClosed {p : Compacts X × X | p.2∈(p.1 : Set X)} := by
  apply isOpen_compl_iff.mp
  apply isOpen_iff_mem_nhds.mpr
  rintro ⟨K,x⟩ hx
  obtain ⟨U,V,hU,hV,hKU,hxV,hUV⟩ := K.isCompact.separation_of_notMem hx
  have hN : {L : Compacts X | (L : Set X)⊆U} ×ˢ V ∈ 𝓝 (K,x) :=
    ((Compacts.isOpen_subsets_of_isOpen hU).prod hV).mem_nhds ⟨hKU,hxV⟩
  apply mem_of_superset hN
  rintro ⟨L,y⟩ ⟨hLU,hyV⟩ hyL
  exact Set.disjoint_left.mp hUV (hLU hyL) hyV

lemma isClosed_preconnected [T2Space X] :
    IsClosed {K : Compacts X | IsPreconnected (K : Set X)} := by
  apply isClosed_of_closure_subset
  intro K hK
  apply (isPreconnected_iff_subset_of_fully_disjoint_closed K.isCompact.isClosed).mpr
  intro u v hu hv hcov huv
  by_contra hn
  push Not at hn
  obtain ⟨x,hx,hxu⟩ := Set.not_subset.mp hn.1
  obtain ⟨y,hy,hyv⟩ := Set.not_subset.mp hn.2
  have hxv := (hcov hx).resolve_left hxu
  have hyu := (hcov hy).resolve_right hyv
  obtain ⟨U,V,hU,hV,hKU,hKV,hUV⟩ := SeparatedNhds.of_isCompact_isCompact
    (K.isCompact.inter_right hu) (K.isCompact.inter_right hv)
    (huv.mono inter_subset_right inter_subset_right)
  let N : Set (Compacts X) := {L | (L : Set X)⊆U∪V} ∩
    {L | ((L : Set X)∩U).Nonempty} ∩ {L | ((L : Set X)∩V).Nonempty}
  have hNo : IsOpen N := ((Compacts.isOpen_subsets_of_isOpen (hU.union hV)).inter
    (Compacts.isOpen_inter_nonempty_of_isOpen hU)).inter
      (Compacts.isOpen_inter_nonempty_of_isOpen hV)
  have hKN : K∈N := by
    refine ⟨⟨?_,y,hy,hKU ⟨hy,hyu⟩⟩,x,hx,hKV ⟨hx,hxv⟩⟩
    intro z hz
    rcases hcov hz with hz' | hz'
    · exact Or.inl (hKU ⟨hz,hz'⟩)
    · exact Or.inr (hKV ⟨hz,hz'⟩)
  obtain ⟨L,hL,hLN⟩ := ((mem_closure_iff_frequently.mp hK).and_eventually
    (hNo.mem_nhds hKN)).exists
  obtain ⟨z,hz,hzU,hzV⟩ := hL U V hU hV hLN.1.1 hLN.1.2 hLN.2
  exact Set.disjoint_left.mp hUV hzU hzV

 

lemma isClosed_local_invariance [T2Space X] {W : Set X} (hW : IsOpen W)
    {f : X → X} (hf : ContinuousOn f W) :
    IsClosed {K : Compacts X | ∀x∈(K : Set X),x∈W → f x∈(K : Set X)} := by
  apply isOpen_compl_iff.mp
  apply isOpen_iff_mem_nhds.mpr
  intro K hK
  simp only [mem_compl_iff,mem_ofPred_eq,not_forall] at hK
  obtain ⟨x,hx,hxW,hfx⟩ := hK
  obtain ⟨U,V,hU,hV,hKU,hfxV,hUV⟩ := K.isCompact.separation_of_notMem hfx
  have hO : IsOpen (W ∩ f ⁻¹' V) := hf.isOpen_inter_preimage hW hV
  have hN : {L : Compacts X | (L : Set X)⊆U} ∩
      {L | ((L : Set X)∩(W ∩ f ⁻¹' V)).Nonempty} ∈ 𝓝 K :=
    ((Compacts.isOpen_subsets_of_isOpen hU).inter
      (Compacts.isOpen_inter_nonempty_of_isOpen hO)).mem_nhds
        ⟨hKU,x,hx,hxW,hfxV⟩
  apply mem_of_superset hN
  rintro L ⟨hLU,y,hy,hyW,hyV⟩ hLf
  exact Set.disjoint_left.mp hUV (hLU (hLf y hy hyW)) hyV

end CompactSetLimits

end

end OAI
