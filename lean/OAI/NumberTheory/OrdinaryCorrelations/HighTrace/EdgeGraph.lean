import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.TreeOccurrences

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.FiniteIntegration
open Finset Classical
variable {S : PrimeSystem} {h ℓ : ℕ}

def edgeGraph (w : ClosedLine h ℓ) (hh : 0 < h) (E : Finset (Fin ℓ)) : SimpleGraph ℤ where
  Adj u v := ∃ e ∈ E, (u = w.offset e.castSucc ∧ v = w.offset e.succ) ∨
    (v = w.offset e.castSucc ∧ u = w.offset e.succ)
  symm := ⟨by rintro u v ⟨e,he,h1 | h2⟩ <;> exact ⟨e,he,by tauto⟩⟩
  loopless := ⟨by
    intro u hu
    obtain ⟨e,he,hu | hu⟩ := hu
    · exact w.endpoints_ne hh e (hu.1.symm.trans hu.2)
    · exact w.endpoints_ne hh e (hu.1.symm.trans hu.2)⟩

lemma edgeGraph_adj (w : ClosedLine h ℓ) (hh : 0 < h) (E : Finset (Fin ℓ))
    (e : Fin ℓ) (he : e ∈ E) :
    (edgeGraph w hh E).Adj (w.offset e.castSucc) (w.offset e.succ) :=
  ⟨e,he,Or.inl ⟨rfl,rfl⟩⟩

def edgeComponents (w : ClosedLine h ℓ) (hh : 0 < h) (E : Finset (Fin ℓ)) :
    Finset (edgeGraph w hh E).ConnectedComponent :=
  E.image (fun e => (edgeGraph w hh E).connectedComponentMk (w.offset e.castSucc))

def componentEdges (w : ClosedLine h ℓ) (hh : 0 < h) (E : Finset (Fin ℓ))
    (c : (edgeGraph w hh E).ConnectedComponent) : Finset (Fin ℓ) :=
  E.filter (fun e => (edgeGraph w hh E).connectedComponentMk (w.offset e.castSucc) = c)

lemma componentEdges_subset (w : ClosedLine h ℓ) (hh : 0 < h) (E : Finset (Fin ℓ))
    (c : (edgeGraph w hh E).ConnectedComponent) : componentEdges w hh E c ⊆ E :=
  filter_subset _ _

lemma componentEdges_nonempty (w : ClosedLine h ℓ) (hh : 0 < h) (E : Finset (Fin ℓ))
    (c : (edgeGraph w hh E).ConnectedComponent) (hc : c ∈ edgeComponents w hh E) :
    (componentEdges w hh E c).Nonempty := by
  obtain ⟨e,he,hc⟩ := mem_image.mp hc
  exact ⟨e,mem_filter.mpr ⟨he,hc⟩⟩

lemma componentEdges_biUnion (w : ClosedLine h ℓ) (hh : 0 < h) (E : Finset (Fin ℓ)) :
    (edgeComponents w hh E).biUnion (componentEdges w hh E) = E := by
  ext e
  constructor
  · intro he
    obtain ⟨c,hc,he⟩ := mem_biUnion.mp he
    exact componentEdges_subset w hh E c he
  · intro he
    exact mem_biUnion.mpr ⟨_,mem_image.mpr ⟨e,he,rfl⟩,mem_filter.mpr ⟨he,rfl⟩⟩

lemma component_vertex_class (w : ClosedLine h ℓ) (hh : 0 < h) (E : Finset (Fin ℓ))
    (c : (edgeGraph w hh E).ConnectedComponent) {v : ℤ}
    (hv : v ∈ edgeVertices w (componentEdges w hh E c)) :
    (edgeGraph w hh E).connectedComponentMk v = c := by
  rcases mem_union.mp hv with hv | hv
  · obtain ⟨e,he,rfl⟩ := mem_image.mp hv
    exact (mem_filter.mp he).2
  · obtain ⟨e,he,rfl⟩ := mem_image.mp hv
    have h := mem_filter.mp he
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      (edgeGraph_adj w hh E e h.1)).symm.trans h.2

lemma component_edges_disjoint (w : ClosedLine h ℓ) (hh : 0 < h) (E : Finset (Fin ℓ))
    {c d : (edgeGraph w hh E).ConnectedComponent} (hcd : c ≠ d) :
    Disjoint (componentEdges w hh E c) (componentEdges w hh E d) := by
  apply disjoint_left.mpr
  intro e he hf
  exact hcd ((mem_filter.mp he).2.symm.trans (mem_filter.mp hf).2)

lemma component_vertices_disjoint (w : ClosedLine h ℓ) (hh : 0 < h) (E : Finset (Fin ℓ))
    {c d : (edgeGraph w hh E).ConnectedComponent} (hcd : c ≠ d) :
    Disjoint (edgeVertices w (componentEdges w hh E c))
      (edgeVertices w (componentEdges w hh E d)) := by
  apply disjoint_left.mpr
  intro v hv hv'
  exact hcd ((component_vertex_class w hh E c hv).symm.trans (component_vertex_class w hh E d hv'))

lemma edgeVertices_biUnion (w : ClosedLine h ℓ) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (E : ι → Finset (Fin ℓ)) :
    edgeVertices w (s.biUnion E) = s.biUnion (fun i => edgeVertices w (E i)) := by
  ext v
  simp only [edgeVertices, mem_union, mem_image, mem_biUnion]
  constructor
  · rintro (⟨e,⟨i,hi,he⟩,hev⟩ | ⟨e,⟨i,hi,he⟩,hev⟩)
    · exact ⟨i,hi,Or.inl ⟨e,he,hev⟩⟩
    · exact ⟨i,hi,Or.inr ⟨e,he,hev⟩⟩
  · rintro ⟨i,hi,hv | hv⟩
    · obtain ⟨e,he,hev⟩ := hv
      exact Or.inl ⟨e,⟨i,hi,he⟩,hev⟩
    · obtain ⟨e,he,hev⟩ := hv
      exact Or.inr ⟨e,⟨i,hi,he⟩,hev⟩

theorem subtreeUnionWeight_components (w : ClosedLine h ℓ) (hh : 0 < h)
    (p : S.Index) (E : Finset (Fin ℓ)) :
    subtreeUnionWeight w p E =
      ∏ c ∈ edgeComponents w hh E, subtreeUnionWeight w p (componentEdges w hh E c) := by
  have hedge : (edgeComponents w hh E : Set _).PairwiseDisjoint (componentEdges w hh E) := by
    intro c hc d hd hcd
    exact component_edges_disjoint w hh E hcd
  have hvertex : (edgeComponents w hh E : Set _).PairwiseDisjoint
      (fun c => edgeVertices w (componentEdges w hh E c)) := by
    intro c hc d hd hcd
    exact component_vertices_disjoint w hh E hcd
  have hcard := card_biUnion hedge
  have hv := edgeVertices_biUnion w (edgeComponents w hh E) (componentEdges w hh E)
  rw [componentEdges_biUnion] at hcard hv
  simp only [subtreeUnionWeight]
  rw [hcard, ← prod_pow_eq_pow_sum, hv, prod_biUnion hvertex, prod_mul_distrib]

lemma active_endpoints_iff (w : ClosedLine h ℓ) (p : S.Index)
    (hph : ¬(p : ℕ) ∣ h) (a : ZMod (p : ℕ)) (e : Fin ℓ) :
    (a + (w.offset e.castSucc : ZMod (p : ℕ)) = 0 ∧
      a + (w.offset e.succ : ZMod (p : ℕ)) = 0) ↔
    ((p : ℕ) ∣ w.label e ∧ a + (w.offset e.castSucc : ZMod (p : ℕ)) = 0) := by
  let : Fact (p : ℕ).Prime := ⟨S.prime_mem p p.property⟩
  constructor
  · rintro ⟨hu,hv⟩
    refine ⟨?_,hu⟩
    have hh0 : (h : ZMod (p : ℕ)) ≠ 0 := (ZMod.natCast_eq_zero_iff h p).not.mpr hph
    have hval : (w.offset e.succ : ZMod (p : ℕ)) = (w.offset e.castSucc : ZMod (p : ℕ)) :=
      add_left_cancel (hv.trans hu.symm)
    have hz : ((w.offset e.succ - w.offset e.castSucc : ℤ) : ZMod (p : ℕ)) = 0 := by
      rw [Int.cast_sub,hval,sub_self]
    rw [w.step] at hz
    push_cast at hz
    have hs : (w.sign e : ZMod (p : ℕ)) ≠ 0 := by
      rcases w.sign_mem e with hs | hs <;> simp [hs]
    have hd := (mul_eq_zero.mp hz).resolve_left (mul_ne_zero hs hh0)
    exact (ZMod.natCast_eq_zero_iff _ _).mp hd
  · rintro ⟨he,hu⟩
    exact ⟨hu, by rwa [w.label_residue_eq e he]⟩

lemma active_graph_exact (w : ClosedLine h ℓ) (hh : 0 < h) (p : S.Index)
    (hph : ¬(p : ℕ) ∣ h) (a : ZMod (p : ℕ)) (u v : ℤ) :
    (edgeGraph w hh (litEdges w p a)).Adj u v ↔
      (edgeGraph w hh w.treeSteps).Adj u v ∧
        a + (u : ZMod (p : ℕ)) = 0 ∧ a + (v : ZMod (p : ℕ)) = 0 := by
  constructor
  · rintro ⟨e,he,huv⟩
    have ht := (mem_filter.mp (mem_filter.mp he).1).1
    refine ⟨⟨e,ht,huv⟩,?_,?_⟩
    · apply lit_vertex_active w p a
      rcases huv with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact mem_union_left _ (mem_image.mpr ⟨e,he,rfl⟩)
      · exact mem_union_right _ (mem_image.mpr ⟨e,he,rfl⟩)
    · apply lit_vertex_active w p a
      rcases huv with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact mem_union_right _ (mem_image.mpr ⟨e,he,rfl⟩)
      · exact mem_union_left _ (mem_image.mpr ⟨e,he,rfl⟩)
  · rintro ⟨⟨e,he,huv⟩,hu,hv⟩
    refine ⟨e,?_,huv⟩
    have ha : a + (w.offset e.castSucc : ZMod (p : ℕ)) = 0 ∧
        a + (w.offset e.succ : ZMod (p : ℕ)) = 0 := by
      rcases huv with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact ⟨hu,hv⟩
      · exact ⟨hv,hu⟩
    have hd := (active_endpoints_iff w p hph a e).mp ha
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨he,hd.1⟩,hd.2⟩

def ActiveConnected (w : ClosedLine h ℓ) (hh : 0 < h) (p : S.Index)
    (a : ZMod (p : ℕ)) : Prop :=
  ∀ u ∈ treeVertices w, ∀ v ∈ treeVertices w,
    a + (u : ZMod (p : ℕ)) = 0 → a + (v : ZMod (p : ℕ)) = 0 →
    (edgeGraph w hh (litEdges w p a)).Reachable u v

lemma singleton_reachable_endpoints (w : ClosedLine h ℓ) (hh : 0 < h)
    (e : Fin ℓ) {v : ℤ}
    (hv : (edgeGraph w hh {e}).Reachable (w.offset e.castSucc) v) :
    v = w.offset e.castSucc ∨ v = w.offset e.succ := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hv
  induction hv with
  | refl => exact Or.inl rfl
  | @tail b c hreach hadj ih =>
    obtain ⟨j,hj,hj' | hj'⟩ := hadj
    · have : j = e := mem_singleton.mp hj
      exact Or.inr (by simpa only [this] using hj'.2)
    · have : j = e := mem_singleton.mp hj
      exact Or.inl (by simpa only [this] using hj'.1)

theorem no_untagged_fixed_center_good_singleton (w : ClosedLine h ℓ) (hh : 0 < h)
    (p : S.Index) (hf : S.IsFixed w p) (hc : ¬S.IsCore p) (a : ZMod (p : ℕ))
    (hall : ∀ i, (p : ℕ) ∣ w.label i → a + (w.offset i.castSucc : ZMod (p : ℕ)) = 0)
    (hconn : ActiveConnected w hh p a) (e : Fin ℓ) (he : w.Good e)
    (hE : litEdges w p a = {e}) : False := by
  have heLit : e ∈ litEdges w p a := by rw [hE]; simp
  have heLit' := mem_filter.mp heLit
  have hsingle : ∀ i, (p : ℕ) ∣ w.label i → i = e := by
    intro i hi
    have hr := hconn (w.offset e.castSucc) (departure_mem_vertices w e)
      (w.offset i.castSucc) (departure_mem_vertices w i) heLit'.2 (hall i hi)
    rw [hE] at hr
    have hend := singleton_reachable_endpoints w hh e hr
    have hit : i ∈ w.treeSteps := by
      by_contra hn
      rcases hend with hend | hend
      · exact (he.2.2.2.2.1 i hn).1 hend
      · exact (he.2.2.2.2.2 i hn).1 hend
    have : i ∈ litEdges w p a := mem_filter.mpr ⟨mem_filter.mpr ⟨hit,hi⟩,hall i hi⟩
    rw [hE] at this
    exact mem_singleton.mp this
  have hcount : S.occurrenceCount w p ≤ 1 := by
    apply (card_le_card (show univ.filter (fun i => (p : ℕ) ∣ w.label i) ⊆ {e} from ?_)).trans
      (by simp)
    intro i hi
    exact mem_singleton.mpr (hsingle i (mem_filter.mp hi).2)
  have hrepeated : 2 ≤ S.occurrenceCount w p := (hf.2.resolve_left hc)
  omega

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
