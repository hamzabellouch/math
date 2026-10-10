import OAI.Probability.BenjaminiSchramm.GhostFanBK

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma openSimpleGraph_delete_singleton (hG : Function.Injective G) (ω : Set E) (e : E) :
    openSimpleGraph G (ω \ {e}) = (openSimpleGraph G ω).deleteEdges {G e} := by
  ext u v
  rw [SimpleGraph.deleteEdges_adj]
  change (u ≠ v ∧ ∃ f ∈ ω \ {e}, G f = s(u,v)) ↔
    (u ≠ v ∧ ∃ f ∈ ω, G f = s(u,v)) ∧ s(u,v) ∉ ({G e} : Set (Sym2 V))
  constructor
  · rintro ⟨hne,f,⟨hfw,hfe⟩,hf⟩
    exact ⟨⟨hne,f,hfw,hf⟩,fun heq => hfe (hG (hf.trans heq))⟩
  · rintro ⟨⟨hne,f,hfw,hf⟩,hfe⟩
    refine ⟨hne,f,⟨hfw,?_⟩,hf⟩
    intro he
    exact hfe (by simpa only [Set.mem_singleton_iff] using (hf.symm.trans (congrArg G he)))

def GhostBridgePivotal (ω : Set E) (m n : Set V) (x : V) (e : E) (u v : V) : Prop :=
  e ∈ ω ∧ G e = s(u,v) ∧ Conn G (ω \ {e}) x u ∧ ¬Conn G (ω \ {e}) x v ∧
    Disjoint (cluster G (ω \ {e}) x) m ∧ Disjoint (cluster G (ω \ {e}) x) n ∧
      (ω \ {e}) ∈ DisjointOccurrence (finiteGhostConnection G v id m)
        (finiteGhostConnection G v id n)

lemma two_ghost_connections_or_pivotal (hG : Function.Injective G) (ω : Set E)
    (m n : Set V) (x : V)
    (hm : ω ∈ finiteGhostConnection G x id m) (hn : ω ∈ finiteGhostConnection G x id n) :
    ω ∈ DisjointOccurrence (finiteGhostConnection G x id m) (finiteGhostConnection G x id n) ∨
      ∃ e u v, GhostBridgePivotal G ω m n x e u v := by
  obtain ⟨a,ha,hxa⟩ := hm
  obtain ⟨b,hb,hxb⟩ := hn
  have hm' : ∃ a ∈ m, (openSimpleGraph G ω).Reachable x a :=
    ⟨a,ha,(conn_iff_reachable G ω x a).mp hxa⟩
  have hn' : ∃ b ∈ n, (openSimpleGraph G ω).Reachable x b :=
    ⟨b,hb,(conn_iff_reachable G ω x b).mp hxb⟩
  rcases two_connections_fan_or_bridge hm' hn' with hfan | ⟨u,v,huv,he,hxu,hA,hB,hfan⟩
  · exact Or.inl (ghostFan_mem_disjointOccurrence G x id (by simpa using hfan))
  right
  obtain ⟨_,e,heω,hGe⟩ := huv
  have hdel : (openSimpleGraph G ω).deleteEdges {s(u,v)} = openSimpleGraph G (ω \ {e}) := by
    rw [← hGe]
    exact (openSimpleGraph_delete_singleton G hG ω e).symm
  have hnot : ¬(openSimpleGraph G (ω \ {e})).Reachable x v := by
    intro hxv
    exact (SimpleGraph.isBridge_iff.mp he) (hxu.symm.trans (hdel.symm ▸ hxv))
  rw [hdel] at hxu hA hB hfan
  refine ⟨e,u,v,heω,hGe,(conn_iff_reachable G _ x u).mpr hxu,
    fun h => hnot ((conn_iff_reachable G _ x v).mp h),?_,?_,?_⟩
  · apply Set.disjoint_left.mpr
    intro y hy hym
    exact hA y hym ((conn_iff_reachable G _ x y).mp hy)
  · apply Set.disjoint_left.mpr
    intro y hy hyn
    exact hB y hyn ((conn_iff_reachable G _ x y).mp hy)
  · exact ghostFan_mem_disjointOccurrence G v id (by simpa using hfan)

lemma measurableSet_ghostBridgePivotal [Countable V] [Countable E]
    (x : V) (e : E) (u v : V) :
    MeasurableSet {z : (Set V × Set V) × Set E |
      GhostBridgePivotal G z.2 z.1.1 z.1.2 x e u v} := by
  have hdel : Measurable (fun ω : Set E => ω \ {e}) :=
    measurable_set_iff.mpr fun f => (measurable_set_mem f).and measurable_const
  have hc (y : V) : Measurable (fun z : (Set V × Set V) × Set E =>
      Conn G (z.2 \ {e}) x y) :=
    (measurableSet_conn G x y).mem.comp (hdel.comp measurable_snd)
  have hm : Measurable (fun z : (Set V × Set V) × Set E =>
      Disjoint (cluster G (z.2 \ {e}) x) z.1.1) := by
    have h := Measurable.forall fun y => (hc y).imp
      (((measurable_set_mem y).comp (measurable_fst.comp measurable_fst)).not)
    simpa only [Set.disjoint_left,cluster,Set.mem_ofPred_eq, Function.comp_def] using h
  have hn : Measurable (fun z : (Set V × Set V) × Set E =>
      Disjoint (cluster G (z.2 \ {e}) x) z.1.2) := by
    have h := Measurable.forall fun y => (hc y).imp
      (((measurable_set_mem y).comp (measurable_snd.comp measurable_fst)).not)
    simpa only [Set.disjoint_left,cluster,Set.mem_ofPred_eq, Function.comp_def] using h
  have hdo := (measurableSet_ghostDisjointOccurrence G v id).preimage
    (measurable_fst.prodMk (hdel.comp measurable_snd))
  exact (((measurable_set_mem e).comp measurable_snd).and
    (measurable_const.and ((hc u).and ((hc v).not.and (hm.and (hn.and hdo.mem)))))).setOf

lemma conn_exterior_witness {ω s : Set E} (x v y : V) (hs : s ⊆ ω)
    (hv : ¬Conn G ω x v) (hvy : Conn G s v y) :
    Conn G (s ∩ internalEdges G (cluster G ω x)ᶜ) v y := by
  have hout (a : V) (ha : Conn G s v a) : a ∉ cluster G ω x := by
    intro hxa
    exact hv (hxa.trans (conn_symm G ω (conn_mono G hs ha)))
  induction hvy with
  | refl => exact conn_refl G _ v
  | @tail a b hva hab ih =>
    obtain ⟨e,he,hGe⟩ := hab
    exact ih.tail ⟨e,⟨he,(mem_internalEdges_of_ends G _ e a b hGe).mpr
      ⟨hout a hva,hout b (hva.tail ⟨e,he,hGe⟩)⟩⟩,hGe⟩

lemma ghostDisjointOccurrence_exterior {ω : Set E} (x v : V) (m n : Set V)
    (hv : ¬Conn G ω x v)
    (h : ω ∈ DisjointOccurrence (finiteGhostConnection G v id m)
      (finiteGhostConnection G v id n)) :
    (ω ∩ internalEdges G (cluster G ω x)ᶜ) ∈
      DisjointOccurrence (finiteGhostConnection G v id m) (finiteGhostConnection G v id n) := by
  let I := internalEdges G (cluster G ω x)ᶜ
  obtain ⟨s,t,hs,ht,hst,⟨a,ha,hva⟩,⟨b,hb,hvb⟩⟩ := h
  let s' := s.filter (fun e => e ∈ I)
  let t' := t.filter (fun e => e ∈ I)
  have hs' : (s' : Set E) = (s : Set E) ∩ I := by ext e; simp [s']
  have ht' : (t' : Set E) = (t : Set E) ∩ I := by ext e; simp [t']
  refine ⟨s',t',?_,?_,?_,?_,?_⟩
  · rw [hs']
    exact Set.inter_subset_inter_left _ hs
  · rw [ht']
    exact Set.inter_subset_inter_left _ ht
  · exact hst.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  · refine ⟨a,ha,?_⟩
    rw [hs']
    exact conn_exterior_witness G x v a hs hv hva
  · refine ⟨b,hb,?_⟩
    rw [ht']
    exact conn_exterior_witness G x v b ht hv hvb

end Percolation.BenjaminiSchramm

end

end OAI
