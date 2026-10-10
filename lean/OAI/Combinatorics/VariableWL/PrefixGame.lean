import OAI.Combinatorics.VariableWL.PrefixWiring

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4

namespace VariableWL.PrefixParts.Data
open VariableWL.Affine
attribute [local instance] Classical.propDecidable
variable {D : Data} {ε : Bit}

def Live (c : Fin D.channels) : D.Vertex ε → Prop
  | .inl _ => False
  | .inr (.inl _) => True
  | .inr (.inr t) => t.channel=c

def observation (c : Fin D.channels) : D.Vertex ε → Vec D.dimension
  | .inl _ => 0
  | .inr (.inl (_,z)) => truncate (D.root c) (z.val ∘ D.order c)
  | .inr (.inr t) => truncate (D.root c) t.bits

theorem live_of_sort {δ : Bit} (c : Fin D.channels) {x : D.Vertex ε} {y : D.Vertex δ}
    (h : sort x=sort y) (hx : Live c x) : Live c y := by
  rcases x with x | (⟨d,z⟩ | t) <;> rcases y with y | (⟨e,w⟩ | u)
  all_goals simp only [sort,Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl] at h
  all_goals try contradiction
  · trivial
  · change t.channel=c at hx
    change u.channel=c
    exact (congrArg Sigma.fst h).symm.trans hx

theorem observation_adj (c : Fin D.channels) {x y : D.Vertex ε}
    (hx : Live c x) (hy : Live c y) (h : (D.graph ε).Adj x y) :
    observation c x=observation c y := by
  rcases x with x | (⟨d,z⟩ | t)
  · exact hx.elim
  · rcases y with y | (⟨e,w⟩ | u)
    · exact hy.elim
    · have hz : z=w := by
        rcases h with h | h
        · exact h.2
        · exact h.2.symm
      subst w
      rfl
    · have he : u.channel=d ∧ u.height=D.dimension ∧ u.bits=z.val ∘ D.order d := by
        simpa only [graph,Forward,false_or] using h
      change u.channel=c at hy
      have hd : d=c := he.1.symm.trans hy
      subst d
      change truncate (D.root c) (z.val ∘ D.order c)=truncate (D.root c) u.bits
      rw [he.2.2]
  · rcases y with y | (⟨e,w⟩ | u)
    · exact hy.elim
    · have he : t.channel=e ∧ t.height=D.dimension ∧ t.bits=w.val ∘ D.order e := by
        simpa only [graph,Forward,or_false] using h
      change t.channel=c at hx
      have hc : e=c := he.1.symm.trans hx
      subst e
      change truncate (D.root c) t.bits=truncate (D.root c) (w.val ∘ D.order c)
      rw [he.2.2]
    · have ht : D.root c ≤ t.height := by rw [← hx]; exact t.property.1
      have hu : D.root c ≤ u.height := by rw [← hy]; exact u.property.1
      change truncate (D.root c) t.bits=truncate (D.root c) u.bits
      rcases h with h | h
      · calc
          _ = truncate (D.root c) (truncate t.height u.bits) := congrArg _ h.2.2.symm
          _ = _ := truncate_truncate ht _
      · calc
          _ = truncate (D.root c) (truncate u.height t.bits) := (truncate_truncate hu _).symm
          _ = _ := congrArg _ h.2.2

end VariableWL.PrefixParts.Data

namespace VariableWL.PrefixParts.Wiring
open VariableWL.Affine VariableWL.SubcubicRealization
attribute [local instance] Classical.propDecidable
variable {B : Type uVariable1} [Fintype B] [FiniteNumbering B] (D : B → Data) [FiniteNumbering (SortTag D)] (W : Wiring D)

omit [FiniteNumbering (SortTag D)] in

theorem within_adj (ε : Bit) (b : B) (x y : (D b).Vertex ε) :
    (W.ports D ε).graph.Adj ⟨b,x⟩ ⟨b,y⟩ ↔ ((D b).graph ε).Adj x y := by
  constructor
  · rintro ⟨i,j,h⟩
    rcases h with ⟨he,hi⟩ | hr | ha
    · exact hi.1
    · obtain ⟨u,v,hu,hv,hm,_⟩ := hr
      have hub : u.1.1=b := (congrArg (fun a : Vertex D ε × Fin 3 => a.1.1) hu).symm
      have hvb : v.1.1=b := (congrArg (fun a : Vertex D ε × Fin 3 => a.1.1) hv).symm
      exact (W.different u.1 (by rw [hm,hub,hvb])).elim
    · rcases ha with ⟨u,v,hu,hv,he⟩ | ⟨u,v,hv,hu,he⟩
      · have hub : b=u := congrArg (fun a : Vertex D ε × Fin 3 => a.1.1) hu
        have hvb : b=v := congrArg (fun a : Vertex D ε × Fin 3 => a.1.1) hv
        rw [← hub,← hvb] at he
        omega
      · have hub : b=u := congrArg (fun a : Vertex D ε × Fin 3 => a.1.1) hv
        have hvb : b=v := congrArg (fun a : Vertex D ε × Fin 3 => a.1.1) hu
        rw [← hub,← hvb] at he
        omega
  · intro h
    exact (partHom D W ε b).map_adj h

end VariableWL.PrefixParts.Wiring

namespace VariableWL.PrefixParts.Data
open VariableWL.Affine
attribute [local instance] Classical.propDecidable
variable {D : Data} {ε : Bit}

abbrev LiveVertex (c : Fin D.channels) (ε : Bit) := {x : D.Vertex ε // Live c x}
def liveGraph (c : Fin D.channels) (ε : Bit) : SimpleGraph (LiveVertex c ε) :=
  (D.graph ε).induce (Live c)

def liveSpine (c d : Fin D.channels) (z : D.Valuation ε) : LiveVertex c ε :=
  ⟨.inr (.inl (d,z)),trivial⟩

def liveTree (c : Fin D.channels) (h : ℕ) (hq : D.root c ≤ h) (ha : h ≤ D.dimension)
    (z : D.Valuation ε) : LiveVertex c ε := ⟨.inr (.inr (Tree.ofValuation c h hq ha z)),rfl⟩

theorem live_tree_to_leaf (c : Fin D.channels) (z : D.Valuation ε) :
    ∀ h (hq : D.root c ≤ h) (ha : h ≤ D.dimension),
    (liveGraph c ε).Reachable (liveTree c h hq ha z)
      (liveTree c D.dimension (D.root_le c) le_rfl z) := by
  intro h hq ha
  induction hd : D.dimension-h generalizing h with
  | zero => have he : h=D.dimension := by omega
            subst h
            exact SimpleGraph.Reachable.refl _
  | succ d ih =>
    have hlt : h<D.dimension := by omega
    have hs : (liveGraph c ε).Adj (liveTree c h hq ha z)
        (liveTree c (h+1) (by omega) (by omega) z) := by
      refine Or.inl ⟨rfl,rfl,?_⟩
      change truncate h (truncate (h+1) (z.val ∘ D.order c))=truncate h (z.val ∘ D.order c)
      exact truncate_truncate (by omega) _
    exact hs.reachable.trans (ih (h+1) (by omega) (by omega) (by omega))

theorem live_spine_to_zero (c d : Fin D.channels) (z : D.Valuation ε) :
    (liveGraph c ε).Reachable (liveSpine c d z) (liveSpine c ⟨0,D.positive⟩ z) := by
  induction hd : d.val generalizing d with
  | zero => have he : d=⟨0,D.positive⟩ := Fin.ext hd
            subst d; exact SimpleGraph.Reachable.refl _
  | succ k ih =>
    let e : Fin D.channels := ⟨k,by omega⟩
    have hs : (liveGraph c ε).Adj (liveSpine c d z) (liveSpine c e z) := Or.inr ⟨hd.symm,rfl⟩
    exact hs.reachable.trans (ih e rfl)

theorem live_to_root (c : Fin D.channels) (z : D.Valuation ε) :
    (liveGraph c ε).Reachable (liveSpine c ⟨0,D.positive⟩ z)
      (liveTree c (D.root c) le_rfl (D.root_le c) z) := by
  have hl : (liveGraph c ε).Adj (liveTree c D.dimension (D.root_le c) le_rfl z) (liveSpine c c z) :=
    Or.inl ⟨rfl,rfl,truncate_full _⟩
  exact (live_spine_to_zero c c z).symm.trans
    (hl.reachable.symm.trans (live_tree_to_leaf c z (D.root c) le_rfl (D.root_le c)).symm)

theorem zero_legal (D : Data) : 0 ∈ D.legal 0 := by
  obtain ⟨ξ,hξ⟩ := D.nonempty 1
  exact (D.coset ξ hξ 0).mpr (by rw [zero_add]; exact hξ)

def zeroValuation (D : Data) : D.Valuation 0 := ⟨0,zero_legal D⟩

end VariableWL.PrefixParts.Data

namespace VariableWL.PrefixParts.Wiring
open VariableWL.Affine VariableWL.SubcubicRealization
attribute [local instance] Classical.propDecidable
variable {B : Type uVariable2} [Fintype B] [FiniteNumbering B] (D : B → Data) [FiniteNumbering (SortTag D)] (W : Wiring D)

def Live (sel : ∀ b, Fin (D b).channels) {ε : Bit} (x : Vertex D ε) : Prop :=
  Data.Live (sel x.1) x.2

def observation (sel : ∀ b, Fin (D b).channels) {ε : Bit} (x : Vertex D ε) : ℕ → Bit :=
  pad (Data.observation (sel x.1) x.2)

omit [FiniteNumbering B] in
theorem live_of_color (sel : ∀ b, Fin (D b).channels) {ε δ : Bit}
    {x : Vertex D ε} {y : Vertex D δ} (h : color D x=color D y) (hx : Live D sel x) : Live D sel y := by
  have hs := (color_eq_iff D x y).mp h
  rcases x with ⟨b,x⟩
  rcases y with ⟨c,y⟩
  have hb : b=c := congrArg Sigma.fst hs
  subst c
  have ht := eq_of_heq (Sigma.mk.inj_iff.mp hs).2
  exact Data.live_of_sort (sel b) ht hx

omit [Fintype B] in
theorem root_observation (sel : ∀ b, Fin (D b).channels) {ε : Bit} (x : RootLabel D ε)
    (hx : Live D sel (rootVertex D x)) : observation D sel (rootVertex D x)=pad x.2.val.bits := by
  change x.2.val.channel=sel x.1.1 at hx
  have hc : x.1.2.val=sel x.1.1 := x.2.property.1.symm.trans hx
  have hh : (D x.1.1).root (sel x.1.1)=x.2.val.height :=
    (congrArg (D x.1.1).root hc.symm).trans x.2.property.2.symm
  change pad (Data.truncate ((D x.1.1).root (sel x.1.1)) x.2.val.bits)=_
  rw [hh,x.2.val.truncated]

omit [FiniteNumbering (SortTag D)] in

theorem observation_adj (sel : ∀ b, Fin (D b).channels) {ε : Bit} {x y : Vertex D ε}
    (hx : Live D sel x) (hy : Live D sel y) (h : (W.ports D ε).graph.Adj x y) :
    observation D sel x=observation D sel y := by
  obtain ⟨i,j,h⟩ := h
  rcases h with hi | hr | ha
  · rcases x with ⟨b,x⟩
    rcases y with ⟨c,y⟩
    obtain ⟨hb,he⟩ := hi
    change b=c at hb
    subst c
    exact congrArg pad (Data.observation_adj (sel b) hx hy he.1)
  · obtain ⟨u,v,hu,hv,_,he⟩ := hr
    have hxu : x=rootVertex D u := congrArg Prod.fst hu
    have hyv : y=rootVertex D v := congrArg Prod.fst hv
    subst x
    subst y
    rw [root_observation D sel u hx,root_observation D sel v hy]
    exact he
  · rcases ha with ⟨b,c,hb,_,_⟩ | ⟨b,c,_,hb,_⟩
    all_goals
      have hxb : x=anchor D ε _ := congrArg Prod.fst hb
      subst x
      exact hx.elim

abbrev LiveVertex (sel : ∀ b, Fin (D b).channels) (ε : Bit) := {x : Vertex D ε // Live D sel x}
noncomputable def liveGraph (sel : ∀ b, Fin (D b).channels) (ε : Bit) :
    SimpleGraph (LiveVertex D sel ε) := (W.ports D ε).graph.induce (Live D sel)

noncomputable def livePartHom (sel : ∀ b, Fin (D b).channels) (ε : Bit) (b : B) :
    Data.liveGraph (sel b) ε →g liveGraph D W sel ε where
  toFun v := ⟨⟨b,v.val⟩,v.property⟩
  map_rel' h := (partHom D W ε b).map_adj h

end VariableWL.PrefixParts.Wiring

namespace VariableWL.PrefixParts.Wiring
open VariableWL.Affine VariableWL.SubcubicRealization
attribute [local instance] Classical.propDecidable
variable {B : Type uVariable3} [Fintype B] [FiniteNumbering B] (D : B → Data) [FiniteNumbering (SortTag D)] (W : Wiring D)

theorem word_of_live_reachable (sel : ∀ b, Fin (D b).channels) {ε δ : Bit}
    {x y : LiveVertex D sel ε} (h : (liveGraph D W sel ε).Reachable x y) :
    ∃ ts, SortWalk (W.ports D ε).graph (color D) ts x.val y.val ∧
      ∀ t ∈ ts, ∀ z : Vertex D δ, color D z=t → Live D sel z := by
  obtain ⟨p⟩ := h
  refine ⟨p.support.map (fun z => color D z.val),?_,?_⟩
  · induction p with
    | nil => exact ⟨rfl,rfl⟩
    | @cons u v w ha p ih =>
      change SortWalk _ _ (color D u.val :: p.support.map (fun z => color D z.val)) u.val w.val
      rw [← p.cons_tail_support] at ih ⊢
      exact ⟨rfl,v.val,ha,ih⟩
  · intro t ht z hz
    obtain ⟨v,_,hv⟩ := List.mem_map.mp ht
    exact live_of_color D sel (hv.trans hz.symm) v.property

theorem observation_sortWalk (sel : ∀ b, Fin (D b).channels) {ε : Bit} (ts : List ℕ)
    (hl : ∀ t ∈ ts, ∀ z : Vertex D ε, color D z=t → Live D sel z)
    {x y : Vertex D ε} (h : SortWalk (W.ports D ε).graph (color D) ts x y) :
    Live D sel x ∧ Live D sel y ∧ observation D sel x=observation D sel y := by
  induction ts using List.twoStepInduction generalizing x y with
  | nil => exact h.elim
  | singleton t =>
    obtain ⟨rfl,hx⟩ := h
    exact ⟨hl t (by simp) x hx,hl t (by simp) x hx,rfl⟩
  | cons_cons t u ts _ ih =>
    obtain ⟨hx,z,hxz,hzy⟩ := h
    have hxL := hl t (by simp) x hx
    have hi := ih u (fun a ha => hl a (List.mem_cons_of_mem t ha)) hzy
    exact ⟨hxL,hi.2.1,(observation_adj D W sel hxL hi.1 hxz).trans hi.2.2⟩

omit [Fintype B] in
def rootOfValuation {ε : Bit} (c : Channel D) (z : (D c.1).Valuation ε) : RootLabel D ε :=
  ⟨c,⟨Data.Tree.ofValuation c.2.val ((D c.1).root c.2.val) le_rfl ((D c.1).root_le _) z,rfl,rfl⟩⟩

omit [Fintype B] in
theorem zero_root_bits (c : Channel D) :
    pad (rootOfValuation D c (Data.zeroValuation (D c.1))).2.val.bits=0 := by
  change pad (Data.truncate ((D c.1).root c.2.val) ((0 : Vec (D c.1).dimension) ∘ (D c.1).order c.2.val))=0
  ext j
  simp [pad,Data.truncate]

omit [Fintype B] in
def queryOwner (b : B) {ε : Bit} (z : (D b).Valuation ε) : Vertex D ε :=
  ⟨b,.inr (.inl (⟨0,(D b).positive⟩,z))⟩

noncomputable def selection (c : Channel D) (b : B) : Fin (D b).channels :=
  if h : b=c.1 then h.symm ▸ c.2.val
  else if h : b=(W.mate c).1 then h.symm ▸ (W.mate c).2.val
  else ⟨0,(D b).positive⟩

omit [Fintype B] in
theorem selection_self (c : Channel D) : selection D W c c.1=c.2.val := by
  simp [selection]

omit [Fintype B] in
theorem selection_mate (c : Channel D) : selection D W c (W.mate c).1=(W.mate c).2.val := by
  simp [selection,W.different c]

omit [FiniteNumbering (SortTag D)] in
theorem zero_queries_reachable (c : Channel D) :
    (liveGraph D W (selection D W c) 0).Reachable
      ⟨queryOwner D c.1 (Data.zeroValuation (D c.1)),trivial⟩
      ⟨queryOwner D (W.mate c).1 (Data.zeroValuation (D (W.mate c).1)),trivial⟩ := by
  let sel := selection D W c
  let x := rootOfValuation D c (Data.zeroValuation (D c.1))
  let y := rootOfValuation D (W.mate c) (Data.zeroValuation (D (W.mate c).1))
  have hx : Live D sel (rootVertex D x) := (selection_self D W c).symm
  have hy : Live D sel (rootVertex D y) := (selection_mate D W c).symm
  have he : (liveGraph D W sel 0).Adj ⟨rootVertex D x,hx⟩ ⟨rootVertex D y,hy⟩ := by
    refine ⟨0,0,Or.inr (Or.inl ⟨x,y,rfl,rfl,rfl,?_⟩)⟩
    exact (zero_root_bits D c).trans (zero_root_bits D (W.mate c)).symm
  have hleft := (Data.live_to_root (sel c.1) (Data.zeroValuation (D c.1))).map
    (livePartHom D W sel 0 c.1)
  have hright := (Data.live_to_root (sel (W.mate c).1) (Data.zeroValuation (D (W.mate c).1))).map
    (livePartHom D W sel 0 (W.mate c).1)
  have hxl : (livePartHom D W sel 0 c.1)
      (Data.liveTree (sel c.1) ((D c.1).root (sel c.1)) le_rfl ((D c.1).root_le _) (Data.zeroValuation (D c.1))) =
      ⟨rootVertex D x,hx⟩ := by
    apply Subtype.ext
    simp only [livePartHom,Data.liveTree,rootVertex,x,rootOfValuation,sel,selection_self]
    rfl
  have hyr : (livePartHom D W sel 0 (W.mate c).1)
      (Data.liveTree (sel (W.mate c).1) ((D (W.mate c).1).root (sel (W.mate c).1)) le_rfl
        ((D (W.mate c).1).root_le _) (Data.zeroValuation (D (W.mate c).1))) =
      ⟨rootVertex D y,hy⟩ := by
    apply Subtype.ext
    simp only [livePartHom,Data.liveTree,rootVertex,y,rootOfValuation,sel,selection_mate]
    rfl
  rw [hxl] at hleft
  rw [hyr] at hright
  exact hleft.trans (he.reachable.trans hright.symm)

theorem readout_word (c : Channel D) :
    ∃ ts, SortWalk (W.ports D 0).graph (color D) ts
      (queryOwner D c.1 (Data.zeroValuation (D c.1)))
      (queryOwner D (W.mate c).1 (Data.zeroValuation (D (W.mate c).1))) ∧
    ∀ x y : Vertex D 1, SortWalk (W.ports D 1).graph (color D) ts x y →
      observation D (selection D W c) x=observation D (selection D W c) y := by
  obtain ⟨ts,hs,ht⟩ := word_of_live_reachable D W (selection D W c) (δ := 1)
    (zero_queries_reachable D W c)
  exact ⟨ts,hs,fun x y h => (observation_sortWalk D W _ ts ht h).2.2⟩

end VariableWL.PrefixParts.Wiring

namespace VariableWL.PrefixParts.Wiring
open VariableWL.Affine VariableWL.SubcubicRealization
attribute [local instance] Classical.propDecidable
variable {B : Type uVariable4} [Fintype B] [FiniteNumbering B] (D : B → Data) [FiniteNumbering (SortTag D)] (W : Wiring D)

noncomputable def query (b : B) : UncoloredVertex D 0 :=
  SubcubicRealization.Vertex.triangle (queryOwner D b (Data.zeroValuation (D b))) 0

abbrev Response (b : B) := (D b).Valuation 1 × Fin 3

noncomputable def response (v : Σ b, Response D b) : UncoloredVertex D 1 :=
  SubcubicRealization.Vertex.triangle (queryOwner D v.1 v.2.1) v.2.2

omit [FiniteNumbering B] in
theorem queryOwner_recognized (b : B) (y : Vertex D 1)
    (h : color D (queryOwner D b (Data.zeroValuation (D b)))=color D y) :
    ∃ z : (D b).Valuation 1, y=queryOwner D b z := by
  have hs := (color_eq_iff D _ _).mp h
  rcases y with ⟨c,y⟩
  have hb : b=c := congrArg Sigma.fst hs
  subst c
  have ht := eq_of_heq (Sigma.mk.inj_iff.mp hs).2
  rcases y with u | (⟨d,z⟩ | t)
  · cases ht
  · have hd : (⟨0,(D b).positive⟩ : Fin (D b).channels)=d := Sum.inl.inj (Sum.inr.inj ht)
    subst d
    exact ⟨z,rfl⟩
  · cases ht

theorem winning_query_recognized {q : ℕ} (hq : 3 ≤ q)
    {p : TypedGame.Position (UncoloredVertex D 0) (UncoloredVertex D 1) q}
    (hp : TypedGame.Winning (uncolored D W 0) (uncolored D W 1) p)
    {i : Fin q} {b : B} {w : UncoloredVertex D 1} (hi : p i=some (query D b,w)) :
    ∃ z : Response D b, w=response D ⟨b,z⟩ := by
  obtain ⟨hw,hc⟩ := winning_color (W.ports D 0) (W.ports D 1) (color D) (color D)
    hq (color_pos D) (color_pos D) hp hi rfl
  obtain ⟨z,hz⟩ := queryOwner_recognized D b w.owner hc
  exact ⟨(z,w.port),SubcubicRealization.Vertex.ext hz rfl hw⟩

theorem winning_readout {q : ℕ} (hq : 3 ≤ q)
    {p : TypedGame.Position (UncoloredVertex D 0) (UncoloredVertex D 1) q}
    (hp : TypedGame.Winning (uncolored D W 0) (uncolored D W 1) p)
    (c : Channel D) (z : Response D c.1) (z' : Response D (W.mate c).1)
    {i j : Fin q} (hi : p i=some (query D c.1,response D ⟨c.1,z⟩))
    (hj : p j=some (query D (W.mate c).1,response D ⟨(W.mate c).1,z'⟩)) :
    pad (Data.truncate ((D c.1).root c.2.val) (z.1.val ∘ (D c.1).order c.2.val))=
    pad (Data.truncate ((D (W.mate c).1).root (W.mate c).2.val)
      (z'.1.val ∘ (D (W.mate c).1).order (W.mate c).2.val)) := by
  obtain ⟨ts,hs,ht⟩ := readout_word D W c
  have h := winning_sortWalk (W.ports D 0) (W.ports D 1) (color D) (color D)
    hq (color_pos D) (color_pos D) ts p hp hi hj ⟨rfl,rfl,hs⟩
  have he := ht _ _ h.2.2
  change pad (Data.truncate ((D c.1).root (selection D W c c.1))
      (z.1.val ∘ (D c.1).order (selection D W c c.1)))=
    pad (Data.truncate ((D (W.mate c).1).root (selection D W c (W.mate c).1))
      (z'.1.val ∘ (D (W.mate c).1).order (selection D W c (W.mate c).1))) at he
  simpa only [selection_self,selection_mate] using he

end VariableWL.PrefixParts.Wiring

end OAI
