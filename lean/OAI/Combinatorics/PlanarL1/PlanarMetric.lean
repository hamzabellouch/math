import OAI.Combinatorics.PlanarL1.Layout

namespace OAI

section



namespace PlanarL1.Topology.Drawing.Split
open Set
variable {V : Type} [LinearOrder V] {G : SimpleGraph V} (D : Drawing G)
  (S : Set (ForwardDart G))

noncomputable def param (p : Piece S) (t : unitInterval) : unitInterval :=
  Icc.convexComb (first S p) (last S p) t

lemma param_injective (p : Piece S) : Function.Injective (param S p) := by
  intro a b he
  apply Subtype.ext
  have hh := congrArg Subtype.val he
  change (1-(a:ℝ))*(first S p:ℝ)+(a:ℝ)*(last S p:ℝ)=
    (1-(b:ℝ))*(first S p:ℝ)+(b:ℝ)*(last S p:ℝ) at hh
  have hp := first_lt_last S p
  nlinarith

lemma param_interior (p : Piece S) (t : unitInterval) (ht : 0<(t:ℝ)) (ht' : (t:ℝ)<1) :
    (first S p:ℝ)<(param S p t:ℝ) ∧ (param S p t:ℝ)<(last S p:ℝ) := by
  have hp := first_lt_last S p
  change (first S p:ℝ)<(1-(t:ℝ))*(first S p:ℝ)+(t:ℝ)*(last S p:ℝ) ∧
    (1-(t:ℝ))*(first S p:ℝ)+(t:ℝ)*(last S p:ℝ)<(last S p:ℝ)
  constructor <;> nlinarith

noncomputable def piecePath (p : Piece S) : Path (point D S (src S p)) (point D S (dst S p)) :=
  ((D.edge (label S p).val.fst (label S p).val.snd (label S p).val.adj).subpath
    (first S p) (last S p)).cast (src_point D S p) (dst_point D S p)

lemma piecePath_apply (p : Piece S) (t : unitInterval) :
    piecePath D S p t=D.edge (label S p).val.fst (label S p).val.snd (label S p).val.adj (param S p t) := rfl

lemma piecePath_injective (p : Piece S) : Function.Injective (piecePath D S p) :=
  (D.edge_injective _ _ _).comp (param_injective S p)

abbrev Directed := Piece S × Bool

def start (d : Directed S) : Node S := if d.2 then dst S d.1 else src S d.1

def finish (d : Directed S) : Node S := if d.2 then src S d.1 else dst S d.1

def flip (d : Directed S) : Directed S := (d.1,!d.2)

lemma start_flip (d : Directed S) : start S (flip S d)=finish S d := by
  rcases d with ⟨p,(_|_)⟩ <;> rfl

lemma finish_flip (d : Directed S) : finish S (flip S d)=start S d := by
  rcases d with ⟨p,(_|_)⟩ <;> rfl

lemma start_ne_finish (D : Drawing G) (d : Directed S) : start S d≠finish S d := by
  rcases d with ⟨p,(_|_)⟩
  · exact src_ne_dst S D p
  · exact (src_ne_dst S D p).symm

noncomputable def arc (d : Directed S) : Path (point D S (start S d)) (point D S (finish S d)) :=
  if h : d.2=true then (piecePath D S d.1).symm.cast (by simp [start,h]) (by simp [finish,h])
  else (piecePath D S d.1).cast (by simp [start,h]) (by simp [finish,h])

lemma arc_injective (d : Directed S) : Function.Injective (arc D S d) := by
  rcases d with ⟨p,(_|_)⟩
  · simpa only [arc,Bool.false_eq_true,↓reduceDIte,Path.cast_coe] using piecePath_injective D S p
  · intro s t he
    have hh : piecePath D S p (unitInterval.symm s)=piecePath D S p (unitInterval.symm t) := he
    apply Subtype.ext
    have hh' := congrArg Subtype.val (piecePath_injective D S p hh)
    change 1-(s:ℝ)=1-(t:ℝ) at hh'
    linarith

lemma arc_location (d : Directed S) (t : unitInterval) (ht : 0<(t:ℝ)) (ht' : (t:ℝ)<1) :
    ∃ r : unitInterval, (first S d.1:ℝ)<(r:ℝ) ∧ (r:ℝ)<(last S d.1:ℝ) ∧
      arc D S d t=D.edge (label S d.1).val.fst (label S d.1).val.snd (label S d.1).val.adj r := by
  rcases d with ⟨p,(_|_)⟩
  · exact ⟨param S p t,(param_interior S p t ht ht').1,(param_interior S p t ht ht').2,rfl⟩
  · have hs : 0<(unitInterval.symm t:ℝ) := by change 0<1-(t:ℝ); linarith
    have hs' : (unitInterval.symm t:ℝ)<1 := by change 1-(t:ℝ)<1; linarith
    exact ⟨param S p (unitInterval.symm t),(param_interior S p _ hs hs').1,
      (param_interior S p _ hs hs').2,rfl⟩

noncomputable def graph : SimpleGraph (Node S) where
  Adj u v := ∃ d : Directed S, start S d=u ∧ finish S d=v
  symm := ⟨by
    rintro u v ⟨d,hu,hv⟩
    exact ⟨flip S d,(start_flip S d).trans hv,(finish_flip S d).trans hu⟩⟩
  loopless := ⟨by
    rintro u ⟨d,hu,hv⟩
    exact start_ne_finish S D d (hu.trans hv.symm)⟩

lemma unsplit_adj (d : ForwardDart G) (hd : d∉S) :
    (graph D S).Adj (.inl d.val.fst) (.inl d.val.snd) :=
  ⟨(.inl ⟨d,hd⟩,false),rfl,rfl⟩

lemma first_adj (d : S) : (graph D S).Adj (.inl d.val.val.fst) (.inr (d,0)) :=
  ⟨(.inr (d,0),false),rfl,rfl⟩

lemma last_adj (d : S) : (graph D S).Adj (.inl d.val.val.snd) (.inr (d,1)) :=
  ⟨(.inr (d,2),true),rfl,rfl⟩

lemma middle_adj (d : S) : (graph D S).Adj (.inr (d,0)) (.inr (d,1)) :=
  ⟨(.inr (d,1),false),rfl,rfl⟩

noncomputable def drawing : Drawing (graph D S) where
  point := point D S
  point_injective := point_injective D S
  edge u v h := (arc D S h.choose).cast (congrArg (point D S) h.choose_spec.1.symm)
    (congrArg (point D S) h.choose_spec.2.symm)
  edge_injective u v h := arc_injective D S h.choose
  interior_avoid := by
    intro u v h t w ht ht' he
    obtain ⟨r,hr,hr',heq⟩ := arc_location D S h.choose t ht ht'
    exact interior_point_avoid D S h.choose.1 hr hr' w (heq.symm.trans he)
  interior_disjoint := by
    intro u v h x y k s t hs hs' ht ht' he
    obtain ⟨r,hr,hr',heq⟩ := arc_location D S h.choose s hs hs'
    obtain ⟨q,hq,hq',heq'⟩ := arc_location D S k.choose t ht ht'
    have hp := interior_piece_unique D S h.choose.1 k.choose.1 hr hr' hq hq'
      (heq.symm.trans (he.trans heq'))
    have hu := h.choose_spec.1
    have hv := h.choose_spec.2
    have hx := k.choose_spec.1
    have hy := k.choose_spec.2
    rcases hh : h.choose with ⟨p,b⟩
    rcases hk : k.choose with ⟨p',b'⟩
    rw [hh,hk] at hp
    change p=p' at hp
    subst p'
    rw [hh] at hu hv
    rw [hk] at hx hy
    cases b <;> cases b' <;> simp only [start,finish,Bool.false_eq_true,↓reduceIte] at hu hv hx hy
    all_goals aesop

end PlanarL1.Topology.Drawing.Split




namespace PlanarL1.Topology.Drawing
variable {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}

noncomputable def pullback (D : Drawing G) (f : W → V) (hf : Function.Injective f)
    (hG : ∀ u v, H.Adj u v → G.Adj (f u) (f v)) : Drawing H where
  point := D.point ∘ f
  point_injective := D.point_injective.comp hf
  edge u v h := D.edge (f u) (f v) (hG u v h)
  edge_injective u v h := D.edge_injective _ _ _
  interior_avoid u v h t w ht ht' := D.interior_avoid _ _ _ t (f w) ht ht'
  interior_disjoint := by
    intro u v h x y k s t hs hs' ht ht' he
    exact (D.interior_disjoint _ _ _ _ _ _ s t hs hs' ht ht' he).elim
      (fun h => Or.inl ⟨hf h.1,hf h.2⟩) (fun h => Or.inr ⟨hf h.1,hf h.2⟩)

end PlanarL1.Topology.Drawing

namespace PlanarL1.Weighted.EnlargedTree
open PlanarL1.Topology PlanarL1.Topology.Drawing
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [LinearOrder V] {G : SimpleGraph V} {l : V → V → ℝ}
  (hc : G.Connected) (hs : ∀ u v, l u v=l v u)
  (hl : ∀ u v, G.Adj u v → 0<l u v) (o : V)

def splitSet : Set (ForwardDart G) :=
  {d | ¬(shortestParents hc hs hl o).graph.Adj d.val.fst d.val.snd}

noncomputable def splitTip (d : ExtraDart hc hs hl o) : Split.Tip (splitSet hc hs hl o) :=
  if h : d.val.fst<d.val.snd then (⟨⟨d.val,h⟩,d.property⟩,0)
  else (⟨⟨d.val.symm,lt_of_le_of_ne (le_of_not_gt h) d.val.adj.ne.symm⟩,
    fun ht => d.property ht.symm⟩,1)

lemma splitTip_injective : Function.Injective (splitTip hc hs hl o) := by
  intro d e he
  by_cases hd : d.val.fst<d.val.snd <;> by_cases hh : e.val.fst<e.val.snd
  · simp only [splitTip,dite_eq_left hd,dite_eq_left hh] at he
    exact Subtype.ext (congrArg (fun t => t.1.val.val) he)
  · have hk := congrArg Prod.snd he
    simp [splitTip,hd,hh] at hk
  · have hk := congrArg Prod.snd he
    simp [splitTip,hd,hh] at hk
  · simp only [splitTip,dite_eq_right hd,dite_eq_right hh] at he
    have hh := congrArg (fun t => t.1.val.val.symm) he
    exact Subtype.ext hh

noncomputable def splitMap : Node hc hs hl o → Split.Node (splitSet hc hs hl o)
  | .inl v => .inl v
  | .inr d => .inr (splitTip hc hs hl o d)

lemma splitMap_injective : Function.Injective (splitMap hc hs hl o) := by
  intro u v he
  cases u with
  | inl u => cases v with
    | inl v => exact congrArg Sum.inl (Sum.inl.inj he)
    | inr v => exact False.elim (Sum.inl_ne_inr he)
  | inr u => cases v with
    | inl v => exact False.elim (Sum.inr_ne_inl he)
    | inr v => exact congrArg Sum.inr (splitTip_injective hc hs hl o (Sum.inr.inj he))

noncomputable def drawingGraph (D : Drawing G) : SimpleGraph (Node hc hs hl o) :=
  SimpleGraph.comap (splitMap hc hs hl o) (Split.graph D (splitSet hc hs hl o))

lemma original_tree_adj (D : Drawing G) {u v : V}
    (h : (shortestParents hc hs hl o).graph.Adj u v) :
    (drawingGraph hc hs hl o D).Adj (.inl u) (.inl v) := by
  have hg := shortestParents.graph_le hc hs hl o h
  by_cases huv : u<v
  · exact Split.unsplit_adj D (splitSet hc hs hl o) ⟨⟨(u,v),hg⟩,huv⟩ (not_not.mpr h)
  · exact (Split.unsplit_adj D (splitSet hc hs hl o)
      ⟨⟨(v,u),hg.symm⟩,lt_of_le_of_ne (le_of_not_gt huv) hg.ne.symm⟩ (not_not.mpr h.symm)).symm

lemma branch_adj (D : Drawing G) (d : ExtraDart hc hs hl o) :
    (drawingGraph hc hs hl o D).Adj (.inl d.val.fst) (.inr d) := by
  change (Split.graph D (splitSet hc hs hl o)).Adj (.inl d.val.fst) (.inr (splitTip hc hs hl o d))
  by_cases hd : d.val.fst<d.val.snd
  · rw [splitTip,dite_eq_left hd]
    exact Split.first_adj D (splitSet hc hs hl o) ⟨⟨d.val,hd⟩,d.property⟩
  · rw [splitTip,dite_eq_right hd]
    exact Split.last_adj D (splitSet hc hs hl o)
      ⟨⟨d.val.symm,lt_of_le_of_ne (le_of_not_gt hd) d.val.adj.ne.symm⟩,fun h => d.property h.symm⟩

lemma tree_le_drawingGraph (D : Drawing G) :
    (tree hc hs hl o).graph ≤ drawingGraph hc hs hl o D := by
  suffices step : ∀ u v, (tree hc hs hl o).Step u v → (drawingGraph hc hs hl o D).Adj u v by
    intro u v h
    exact h.elim (step u v) (fun h => (step v u h).symm)
  intro u v h
  obtain ⟨hv,rfl⟩ := h
  cases v with
  | inl v =>
    apply original_tree_adj hc hs hl o D
    exact Or.inr ⟨fun he => hv (congrArg Sum.inl he),rfl⟩
  | inr d => exact branch_adj hc hs hl o D d

lemma pair_adj (D : Drawing G) (d : ExtraDart hc hs hl o) :
    (drawingGraph hc hs hl o D).Adj (.inr d) (.inr (ExtraDart.reverse hc hs hl o d)) := by
  change (Split.graph D (splitSet hc hs hl o)).Adj (.inr (splitTip hc hs hl o d))
    (.inr (splitTip hc hs hl o (ExtraDart.reverse hc hs hl o d)))
  unfold splitTip
  by_cases hd : d.val.fst<d.val.snd
  · have hn : ¬(ExtraDart.reverse hc hs hl o d).val.fst<
        (ExtraDart.reverse hc hs hl o d).val.snd := not_lt_of_gt hd
    rw [dite_eq_left hd,dite_eq_right hn]
    exact Split.middle_adj D (splitSet hc hs hl o) ⟨⟨d.val,hd⟩,d.property⟩
  · have hh : (ExtraDart.reverse hc hs hl o d).val.fst<
        (ExtraDart.reverse hc hs hl o d).val.snd := lt_of_le_of_ne (le_of_not_gt hd) d.val.adj.ne.symm
    rw [dite_eq_right hd,dite_eq_left hh]
    exact (Split.middle_adj D (splitSet hc hs hl o)
      ⟨⟨d.val.symm,hh⟩, fun h => d.property h.symm⟩).symm

noncomputable def enlargedDrawing (D : Drawing G) : Drawing (drawingGraph hc hs hl o D) :=
  (Split.drawing D (splitSet hc hs hl o)).pullback (splitMap hc hs hl o)
    (splitMap_injective hc hs hl o) (fun _ _ h => h)

end PlanarL1.Weighted.EnlargedTree




namespace PlanarL1.Weighted.EnlargedTree
open PlanarL1.Topology
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] {G : SimpleGraph V} {l : V → V → ℝ}
  (hc : G.Connected) (hs : ∀ u v, l u v=l v u)
  (hl : ∀ u v, G.Adj u v → 0<l u v) (o : V)

lemma reverse_ne (d : ExtraDart hc hs hl o) : ExtraDart.reverse hc hs hl o d≠d := by
  intro he
  have hh := congrArg (fun d : ExtraDart hc hs hl o => d.val.fst) he
  exact d.val.adj.ne hh.symm

noncomputable def matchingGraph : SimpleGraph {v : Node hc hs hl o // (tree hc hs hl o).IsLeaf v} where
  Adj i j := ∃ d : ExtraDart hc hs hl o, i.val=.inr d ∧ j.val=.inr (ExtraDart.reverse hc hs hl o d)
  symm := ⟨by
    rintro i j ⟨d,hi,hj⟩
    refine ⟨ExtraDart.reverse hc hs hl o d,hj,?_⟩
    rw [ExtraDart.reverse_reverse]; exact hi⟩
  loopless := ⟨by
    rintro i ⟨d,hi,hj⟩
    exact reverse_ne hc hs hl o d (Sum.inr.inj (hj.symm.trans hi))⟩

lemma matchingGraph_height (i j : {v : Node hc hs hl o // (tree hc hs hl o).IsLeaf v})
    (h : (matchingGraph hc hs hl o).Adj i j) :
    (tree hc hs hl o).height i.val=(tree hc hs hl o).height j.val := by
  obtain ⟨d,hi,hj⟩ := h
  rw [hi,hj]
  exact (ExtraDart.tipHeight_reverse hc hs hl o d).symm

lemma matchingGraph_matching (i j k : {v : Node hc hs hl o // (tree hc hs hl o).IsLeaf v})
    (h : (matchingGraph hc hs hl o).Adj i j) (h' : (matchingGraph hc hs hl o).Adj i k) : j=k := by
  obtain ⟨d,hi,hj⟩ := h
  obtain ⟨e,hi',hk⟩ := h'
  have he : d=e := Sum.inr.inj (hi.symm.trans hi')
  subst e
  exact Subtype.ext (hj.trans hk.symm)

lemma layout_of_planar [LinearOrder V] (hp : IsPlanar G)
    (hroot : ¬(tree hc hs hl o).IsLeaf (tree hc hs hl o).root) :
    ∃ n : ℕ, ∃ L : (tree hc hs hl o).Layout n, ExactPairs L := by
  classical
  let : LinearOrder (Node hc hs hl o) := LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective
  obtain ⟨D⟩ := drawing_of_planar hp
  obtain ⟨P,_⟩ := (enlargedDrawing hc hs hl o D).polygonal
  obtain ⟨L,hL⟩ := (tree hc hs hl o).layout_of_drawing P (tree_le_drawingGraph hc hs hl o D)
    hroot (matchingGraph hc hs hl o) (by
      rintro i j ⟨d,hi,hj⟩
      rw [hi,hj]
      exact pair_adj hc hs hl o D d)
    (matchingGraph_height hc hs hl o) (matchingGraph_matching hc hs hl o)
  exact ⟨_,L,hL⟩

end PlanarL1.Weighted.EnlargedTree

namespace PlanarL1.HeightTree
variable {V : Type} [Fintype V] (T : HeightTree V) (hroot : T.IsLeaf T.root)

noncomputable def rootLeafLayout : T.Layout 1 where
  leaf := fun _ => T.root
  isLeaf := fun _ => hroot
  injective := fun _ _ _ => Subsingleton.elim _ _
  covers := fun v _ => ⟨0,hroot.ancestor_eq (T.root_ancestor v)⟩
  prefix_connected := by
    intro a i j hi hj
    have he : i=j := Subsingleton.elim _ _
    subst j
    exact .rfl
  pair := ⊥
  noncrossing := fun _ _ _ _ _ _ _ h => h.1
  paired_height := fun _ _ h => h.elim
  matching := fun _ _ _ h => h.elim

end PlanarL1.HeightTree

namespace PlanarL1.Weighted.EnlargedTree
open PlanarL1.Topology
variable {V : Type} [Fintype V] {G : SimpleGraph V} {l : V → V → ℝ}
  (hc : G.Connected) (hs : ∀ u v, l u v=l v u)
  (hl : ∀ u v, G.Adj u v → 0<l u v) (o : V)

/-- The source's exact topology-to-column-layout bridge, including a singleton
incidence tree. The contour and the noncrossing switches are constructed, not
assumed. -/
lemma exact_layout_of_planar (hp : IsPlanar G) :
    ∃ n : ℕ, ∃ L : (tree hc hs hl o).Layout n, ExactPairs L := by
  classical
  let : LinearOrder V := LinearOrder.lift' (Fintype.equivFin V) (Fintype.equivFin V).injective
  by_cases hr : (tree hc hs hl o).IsLeaf (tree hc hs hl o).root
  · refine ⟨1,(tree hc hs hl o).rootLeafLayout hr,?_⟩
    intro i j
    constructor
    · intro h; exact h.elim
    · rintro ⟨d,_,_⟩
      have he := hr.ancestor_eq ((tree hc hs hl o).root_ancestor (.inr d))
      exact False.elim (Sum.inl_ne_inr he)
  · exact layout_of_planar hc hs hl o hp hr

/-- Every literal planar weighted graph is isometric on its original vertices
to the constructed terminal noncrossing column model. -/
lemma column_model_of_planar (hp : IsPlanar G) :
    ∃ n : ℕ, ∃ L : (tree hc hs hl o).Layout n, ExactPairs L ∧
      ∀ u v : V, (L.point (.inl u)).distance (L.point (.inl v))=graphDistance G l u v := by
  obtain ⟨n,L,hL⟩ := exact_layout_of_planar hc hs hl o hp
  exact ⟨n,L,hL,original_distance L hL⟩

end PlanarL1.Weighted.EnlargedTree


end

end OAI
