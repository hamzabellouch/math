import Mathlib

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.PortSubdivision

structure PortGraph (V D : Type*) where
  origin : D → V
  reverse : D → D
  reverse_reverse : Function.Involutive reverse
  reverse_ne : ∀ d, reverse d ≠ d

namespace PortGraph
variable {V D : Type*} (Γ : PortGraph V D)

@[simp] theorem reverse_reverse_apply (d : D) : Γ.reverse (Γ.reverse d) = d :=
  Γ.reverse_reverse d

/-- The canonical threefold subdivision, including loops and parallel edges. -/
def subdivision : SimpleGraph (V ⊕ D) where
  Adj a b := match a,b with
    | .inl _, .inl _ => False
    | .inl v, .inr d => Γ.origin d = v
    | .inr d, .inl v => Γ.origin d = v
    | .inr d, .inr e => Γ.reverse d = e
  symm := ⟨by
    intro a b h
    cases a with
    | inl v => cases b <;> exact h
    | inr d =>
      cases b with
      | inl v => exact h
      | inr e =>
        change Γ.reverse e = d
        change Γ.reverse d = e at h
        rw [← h,Γ.reverse_reverse]⟩
  loopless := ⟨by
    intro a h
    cases a with
    | inl v => exact h
    | inr d => exact Γ.reverse_ne d h⟩

@[simp] theorem adj_original (v w : V) : ¬ Γ.subdivision.Adj (.inl v) (.inl w) := id
@[simp] theorem adj_original_port (v : V) (d : D) :
    Γ.subdivision.Adj (.inl v) (.inr d) ↔ Γ.origin d = v := Iff.rfl
@[simp] theorem adj_port_original (v : V) (d : D) :
    Γ.subdivision.Adj (.inr d) (.inl v) ↔ Γ.origin d = v := Iff.rfl
@[simp] theorem adj_ports (d e : D) :
    Γ.subdivision.Adj (.inr d) (.inr e) ↔ Γ.reverse d = e := Iff.rfl

theorem port_adj_iff (d : D) (a : V ⊕ D) :
    Γ.subdivision.Adj (.inr d) a ↔ a = .inl (Γ.origin d) ∨ a = .inr (Γ.reverse d) := by
  cases a <;> simp [eq_comm]

/-- Every cycle through a port uses its middle edge, since the other port
neighbor is unique and the cycle cannot immediately backtrack. -/
theorem cycle_middle_at_port (d : D) (p : Γ.subdivision.Walk (.inr d) (.inr d))
    (hp : p.IsCycle) : s(Sum.inr d,Sum.inr (Γ.reverse d)) ∈ p.edges := by
  have ha := (Γ.port_adj_iff d p.snd).mp (p.adj_snd hp.not_nil)
  have hb := (Γ.port_adj_iff d p.penultimate).mp (p.adj_penultimate hp.not_nil).symm
  rcases ha with ha | ha
  · rcases hb with hb | hb
    · exact False.elim (hp.snd_ne_penultimate (ha.trans hb.symm))
    · have he := p.mk_penultimate_end_mem_edges hp.not_nil
      rw [hb,Sym2.eq_swap] at he
      exact he
  · simpa only [ha] using p.mk_start_snd_mem_edges hp.not_nil

/-- No cycle lives entirely in the spokes; a short cycle always gives a
middle edge eligible for a matching transposition. -/
theorem cycle_has_middle [DecidableEq V] [DecidableEq D] {a : V ⊕ D}
    (p : Γ.subdivision.Walk a a) (hp : p.IsCycle) :
    ∃ d, s(Sum.inr d,Sum.inr (Γ.reverse d)) ∈ p.edges := by
  have hex : ∃ d, Sum.inr d ∈ p.support := by
    cases a with
    | inr d => exact ⟨d,p.start_mem_support⟩
    | inl v =>
      have ha := p.adj_snd hp.not_nil
      cases hs : p.snd with
      | inl w => rw [hs] at ha; exact False.elim ha
      | inr d => exact ⟨d,hs ▸ p.snd_mem_support_of_mem_edges (p.mk_start_snd_mem_edges hp.not_nil)⟩
  obtain ⟨d,hd⟩ := hex
  refine ⟨d,?_⟩
  have he := Γ.cycle_middle_at_port d (p.rotate (.inr d) hd) (hp.rotate hd)
  exact (p.rotate_edges (.inr d) hd).mem_iff.mp he

/-- The neighbor fiber at an original vertex is exactly its port fiber. -/
def originalNeighborEquiv (v : V) :
    Γ.subdivision.neighborSet (.inl v) ≃ {d : D // Γ.origin d = v} where
  toFun n := match n with
    | ⟨.inl _,h⟩ => False.elim h
    | ⟨.inr d,h⟩ => ⟨d,h⟩
  invFun d := ⟨.inr d.val,d.property⟩
  left_inv n := by rcases n with ⟨v|d,h⟩; exact False.elim h; rfl
  right_inv _ := rfl

/-- A port has exactly two neighbors: its original vertex and its reverse port.
They lie in disjoint summands even when the original edge is a graph loop. -/
def portNeighborEquiv (d : D) : Γ.subdivision.neighborSet (.inr d) ≃ Bool where
  toFun n := match n.val with | .inl _ => false | .inr _ => true
  invFun b := if b then ⟨.inr (Γ.reverse d),rfl⟩ else ⟨.inl (Γ.origin d),rfl⟩
  left_inv n := by
    rcases n with ⟨v|e,h⟩
    · apply Subtype.ext
      exact congrArg Sum.inl h
    · apply Subtype.ext
      exact congrArg Sum.inr h
  right_inv b := by cases b <;> rfl

theorem card_original_neighbors (v : V) :
    Nat.card (Γ.subdivision.neighborSet (.inl v)) =
      Nat.card {d : D // Γ.origin d = v} := Nat.card_congr (Γ.originalNeighborEquiv v)

theorem card_port_neighbors (d : D) : Nat.card (Γ.subdivision.neighborSet (.inr d)) = 2 := by
  rw [Nat.card_congr (Γ.portNeighborEquiv d)]
  simp

/-- Conjugating the reversal while keeping port origins fixed is a
matching switch, not a relabeling of the original graph. -/
def moveMatches (σ : Equiv.Perm D) : PortGraph V D where
  origin := Γ.origin
  reverse d := σ (Γ.reverse (σ.symm d))
  reverse_reverse d := by simp
  reverse_ne d := by
    intro h
    have h' := congrArg σ.symm h
    simp only [Equiv.symm_apply_apply] at h'
    exact Γ.reverse_ne (σ.symm d) h'

section Switching
variable [DecidableEq D]

/-- Transpose two equally oriented ports. Their reverse ports are not moved. -/
def switch (d e : D) : PortGraph V D := Γ.moveMatches (Equiv.swap d e)

@[simp] theorem switch_origin (d e f : D) : (Γ.switch d e).origin f = Γ.origin f := rfl

theorem switch_reverse_left (d e : D) (hde : Γ.reverse e ≠ d)
    (hee : Γ.reverse e ≠ e) : (Γ.switch d e).reverse d = Γ.reverse e := by
  simp [switch,moveMatches,Equiv.swap_apply_of_ne_of_ne hde hee]

theorem switch_reverse_right (d e : D) (hdd : Γ.reverse d ≠ d)
    (hde : Γ.reverse d ≠ e) : (Γ.switch d e).reverse e = Γ.reverse d := by
  simp [switch,moveMatches,Equiv.swap_apply_of_ne_of_ne hdd hde]

theorem switch_reverse_unchanged (d e f : D) (hfd : f ≠ d) (hfe : f ≠ e)
    (hrd : Γ.reverse f ≠ d) (hre : Γ.reverse f ≠ e) :
    (Γ.switch d e).reverse f = Γ.reverse f := by
  simp [switch,moveMatches,Equiv.swap_apply_of_ne_of_ne hfd hfe,
    Equiv.swap_apply_of_ne_of_ne hrd hre]

/-- The subdivision changes exactly the two middle edges, preserving every
origin-port incidence, including incidences belonging to original loops. -/
theorem switch_adj (d e : D) (hde : d ≠ e) (hdr : d ≠ Γ.reverse e)
    (a b : V ⊕ D) :
    (Γ.switch d e).subdivision.Adj a b ↔
      (Γ.subdivision.Adj a b ∧ s(a,b) ≠ s(Sum.inr d,Sum.inr (Γ.reverse d)) ∧
        s(a,b) ≠ s(Sum.inr e,Sum.inr (Γ.reverse e))) ∨
      s(a,b) = s(Sum.inr d,Sum.inr (Γ.reverse e)) ∨
      s(a,b) = s(Sum.inr e,Sum.inr (Γ.reverse d)) := by
  have hrd : Γ.reverse d ≠ d := Γ.reverse_ne d
  have hre : Γ.reverse e ≠ e := Γ.reverse_ne e
  have hrd_e : Γ.reverse d ≠ e := by
    intro h
    apply hdr
    rw [← h,Γ.reverse_reverse]
  have hrev : Γ.reverse d ≠ Γ.reverse e := fun h => hde (Γ.reverse_reverse.injective h)
  cases a with
  | inl a =>
    cases b <;> simp [subdivision,switch_origin]
  | inr f =>
    cases b with
    | inl b => simp [subdivision,switch_origin]
    | inr g =>
      change (Equiv.swap d e) (Γ.reverse ((Equiv.swap d e) f)) = g ↔ _
      simp only [adj_ports,Sym2.eq_iff,Sum.inr.injEq]
      by_cases hfd : f = d
      · subst f
        simp only [Equiv.swap_apply_left,Equiv.swap_apply_of_ne_of_ne hdr.symm hre]
        grind
      · by_cases hfe : f = e
        · subst f
          simp only [Equiv.swap_apply_right,Equiv.swap_apply_of_ne_of_ne hrd hrd_e]
          grind
        · by_cases hfrd : f = Γ.reverse d
          · subst f
            simp only [Equiv.swap_apply_of_ne_of_ne hrd hrd_e,reverse_reverse_apply,
              Equiv.swap_apply_left]
            grind
          · by_cases hfre : f = Γ.reverse e
            · subst f
              simp only [Equiv.swap_apply_of_ne_of_ne hdr.symm hre,reverse_reverse_apply,
                Equiv.swap_apply_right]
              grind
            · have hrfd : Γ.reverse f ≠ d := by
                intro h
                apply hfrd
                rw [← h,Γ.reverse_reverse]
              have hrfe : Γ.reverse f ≠ e := by
                intro h
                apply hfre
                rw [← h,Γ.reverse_reverse]
              simp [Equiv.swap_apply_of_ne_of_ne hfd hfe,
                Equiv.swap_apply_of_ne_of_ne hrfd hrfe,hfd,hfe,hfrd,hfre]

/-- Transposing two occurrences of the same label preserves every port label. -/
theorem label_swap {T : Type*} (label : D → T) (d e : D) (h : label d = label e)
    (f : D) : label ((Equiv.swap d e) f) = label f := by
  by_cases hfd : f = d
  · subst f; simpa using h.symm
  · by_cases hfe : f = e
    · subst f; simpa using h
    · rw [Equiv.swap_apply_of_ne_of_ne hfd hfe]

theorem switch_preserves_labels {T : Type*} (label : D → T) (bar : T → T)
    (hlabel : ∀ f, label (Γ.reverse f) = bar (label f))
    (d e : D) (h : label d = label e) (f : D) :
    label ((Γ.switch d e).reverse f) = bar (label f) := by
  change label ((Equiv.swap d e) (Γ.reverse ((Equiv.swap d e) f))) = bar (label f)
  rw [label_swap label d e h, hlabel, label_swap label d e h]

end Switching

/-- Multigraph walks remember the traversed port, not just endpoint vertices. -/
inductive Walk : V → V → Type _
  | nil (v : V) : Walk v v
  | cons {v w : V} (d : D) (hd : Γ.origin d = v)
      (p : Walk (Γ.origin (Γ.reverse d)) w) : Walk v w

namespace Walk
variable {Γ} {a b c : V}

def length {a b : V} : Γ.Walk a b → ℕ
  | .nil _ => 0
  | .cons _ _ p => p.length + 1

def darts {a b : V} : Γ.Walk a b → List D
  | .nil _ => []
  | .cons d _ p => d :: p.darts

def append {a b c : V} : Γ.Walk a b → Γ.Walk b c → Γ.Walk a c
  | .nil _,q => q
  | .cons d hd p,q => .cons d hd (p.append q)

@[simp] theorem length_darts (p : Γ.Walk a b) : p.darts.length = p.length := by
  induction p <;> simp_all [darts,length]

@[simp] theorem length_append (p : Γ.Walk a b) (q : Γ.Walk b c) :
    (p.append q).length = p.length + q.length := by
  induction p with
  | nil => simp [append,length]
  | cons d hd p ih => simp only [append,length,ih]; omega

/-- Source immersion is exactly nonbacktracking of consecutive ports. -/
def IsReduced (p : Γ.Walk a b) : Prop :=
  p.darts.IsChain (fun d e => e ≠ Γ.reverse d)

/-- No changes to endpoints or to the original multigraph are made by subdividing. -/
def toSubdivision {a b : V} : Γ.Walk a b → Γ.subdivision.Walk (.inl a) (.inl b)
  | .nil a => .nil
  | .cons d hd p =>
    .cons (show Γ.subdivision.Adj (.inl a) (.inr d) from hd)
      (.cons (show Γ.subdivision.Adj (.inr d) (.inr (Γ.reverse d)) from rfl)
        (.cons (show Γ.subdivision.Adj (.inr (Γ.reverse d)) (.inl (Γ.origin (Γ.reverse d))) from rfl) p.toSubdivision))

@[simp] theorem length_toSubdivision (p : Γ.Walk a b) :
    p.toSubdivision.length = 3 * p.length := by
  induction p with
  | nil => rfl
  | cons d hd p ih => simp only [toSubdivision,SimpleGraph.Walk.length_cons,length,ih]; omega

@[simp] theorem toSubdivision_append (p : Γ.Walk a b) (q : Γ.Walk b c) :
    (p.append q).toSubdivision = p.toSubdivision.append q.toSubdivision := by
  induction p with
  | nil => rfl
  | cons d hd p ih => simp only [append,toSubdivision,SimpleGraph.Walk.cons_append,ih]

/-- Immersion of the original port path is preserved by the subdivision.
In particular the encoding does not spuriously remove a short circuit. -/
theorem reduced_toSubdivision (p : Γ.Walk a b) (hp : p.IsReduced) :
    p.toSubdivision.edges.IsChain (· ≠ ·) := by
  induction p with
  | nil => simp [toSubdivision]
  | @cons a b d hd p ih =>
    cases p with
    | nil =>
      simp [toSubdivision, SimpleGraph.Walk.edges_cons, List.isChain_cons_cons]
    | cons e he q =>
      have hp' : (Walk.cons e he q).IsReduced := by
        exact (List.isChain_cons.mp hp).2
      have hde : e ≠ Γ.reverse d := by
        exact (List.isChain_cons_cons.mp hp).1
      have hi := ih hp'
      simp only [toSubdivision, SimpleGraph.Walk.edges_cons] at hi ⊢
      simp only [List.isChain_cons_cons] at hi ⊢
      refine ⟨?_, ?_, ?_, hi⟩
      · simp
      · simp
      · simpa using Ne.symm hde

end Walk
end PortGraph
end TorsionFreeZeroDivisors.PortSubdivision

/-!
Quantitative edge switching for the girth conditioning in types.tex 116–147.
The simple-graph lemmas are also applicable to the canonical threefold
subdivision of a port multigraph (loops become triangles). No random-graph
existence or cone-topology conclusion is assumed in these lemmas.
-/

namespace TorsionFreeZeroDivisors.GirthSwitch

open SimpleGraph
open scoped ENNReal

variable {V : Type*} {G H : SimpleGraph V} {a b x y : V}

/-- Decompose at a specified edge occurrence, with its actual orientation. -/
theorem split_at_edge (p : G.Walk a b) (e : Sym2 V) (he : e ∈ p.edges) :
    ∃ (x y : V) (hxy : G.Adj x y) (p₁ : G.Walk a x) (p₂ : G.Walk y b),
      s(x,y) = e ∧ p = p₁.append (.cons hxy p₂) := by
  induction p with
  | nil => simp at he
  | @cons u v w huv p ih =>
    simp only [Walk.edges_cons, List.mem_cons] at he
    rcases he with he | he
    · exact ⟨u,v,huv,.nil,p,he.symm,rfl⟩
    · obtain ⟨x,y,hxy,p₁,p₂,hxe,hp⟩ := ih he
      exact ⟨x,y,hxy,.cons huv p₁,p₂,hxe,by rw [hp]; rfl⟩

/-- Removing an edge of a closed trail leaves an alternate walk one shorter,
without using the removed edge. -/
theorem alternate_walk (p : G.Walk a a) (hp : p.IsTrail)
    (e : Sym2 V) (he : e ∈ p.edges) :
    ∃ (x y : V) (q : G.Walk x y),
      s(x,y) = e ∧ e ∉ q.edges ∧ q.length + 1 = p.length := by
  obtain ⟨x,y,hxy,p₁,p₂,hxe,hpdecomp⟩ := split_at_edge p e he
  subst p
  have hn := hp.edges_nodup
  simp only [Walk.edges_append, Walk.edges_cons, List.nodup_append,
    List.nodup_cons] at hn
  have hleft : e ∉ p₁.edges := by
    intro ht
    exact hn.2.2 e ht e (by simp [hxe]) rfl
  have hright : e ∉ p₂.edges := by simpa only [hxe] using hn.2.1.1
  refine ⟨y,x,p₂.append p₁,?_,?_,?_⟩
  · simpa only [Sym2.eq_swap] using hxe
  · simp only [Walk.edges_append, List.mem_append, not_or]
    exact ⟨hright,hleft⟩
  · simp only [Walk.length_append, Walk.length_cons]
    omega

/-- Adjoining one new edge. -/
def addEdge (G : SimpleGraph V) (x y : V) : SimpleGraph V :=
  G ⊔ SimpleGraph.fromEdgeSet {s(x,y)}

@[simp] theorem addEdge_adj (u v : V) :
    (addEdge G x y).Adj u v ↔ G.Adj u v ∨ (s(u,v) = s(x,y) ∧ u ≠ v) := by
  simp [addEdge, SimpleGraph.fromEdgeSet_adj]

/-- A walk avoiding the newly adjoined edge lies in the old graph. -/
theorem transfer_addEdge (p : (addEdge G x y).Walk a b)
    (hp : s(x,y) ∉ p.edges) :
    ∃ q : G.Walk a b, q.length = p.length := by
  refine ⟨p.transfer G ?_,Walk.length_transfer ..⟩
  intro e he
  have hg := p.edges_subset_edgeSet he
  simp only [addEdge, SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_fromEdgeSet,
    Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff] at hg
  rcases hg with hg | ⟨rfl,_⟩
  · exact hg
  · exact False.elim (hp he)

/-- Adding an edge whose endpoints have no short old connecting path preserves
the lower girth bound. The path hypothesis includes either orientation. -/
theorem girth_addEdge (L : ℕ) (hG : (L : ℕ∞) ≤ G.egirth)
    (hx : ∀ p : G.Walk x y, L ≤ p.length + 1) :
    (L : ℕ∞) ≤ (addEdge G x y).egirth := by
  classical
  rw [SimpleGraph.le_egirth]
  intro a p hp
  by_cases he : s(x,y) ∈ p.edges
  · obtain ⟨u,v,q,huv,hqe,hql⟩ := alternate_walk p hp.isTrail _ he
    obtain ⟨q',hq'⟩ := transfer_addEdge q hqe
    have ho : (u = x ∧ v = y) ∨ (u = y ∧ v = x) := by
      simpa only [Sym2.eq_iff] using huv
    have hl : L ≤ q'.length + 1 := by
      rcases ho with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hx q'
      · simpa only [Walk.length_reverse] using hx q'.reverse
    rw [hq',hql] at hl
    exact_mod_cast hl
  · have htransfer : ∀ e, e ∈ p.edges → e ∈ G.edgeSet := by
      intro e he'
      have hg := p.edges_subset_edgeSet he'
      simp only [addEdge, SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_fromEdgeSet,
        Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff] at hg
      rcases hg with hg | ⟨rfl,_⟩
      · exact hg
      · exact False.elim (he he')
    have hh := SimpleGraph.le_egirth.mp hG a (p.transfer G htransfer) (hp.transfer htransfer)
    simpa only [Walk.length_transfer] using hh

/-- Before the first occurrence of a new edge, a walk lies wholly in G.
No simplicity assumption is required for this decomposition. -/
theorem first_new_edge (p : (addEdge G x y).Walk a b) :
    (∃ q : G.Walk a b, q.length ≤ p.length) ∨
    (∃ q : G.Walk a x, q.length + 1 ≤ p.length) ∨
    (∃ q : G.Walk a y, q.length + 1 ≤ p.length) := by
  induction p with
  | nil => exact Or.inl ⟨.nil,le_rfl⟩
  | @cons u v w huv p ih =>
    rcases (addEdge_adj u v).mp huv with hold | ⟨he,_⟩
    · rcases ih with ⟨q,hq⟩ | ⟨q,hq⟩ | ⟨q,hq⟩
      · exact Or.inl ⟨.cons hold q, by simpa only [Walk.length_cons] using Nat.add_le_add_right hq 1⟩
      · exact Or.inr (Or.inl ⟨.cons hold q, by simp only [Walk.length_cons]; omega⟩)
      · exact Or.inr (Or.inr ⟨.cons hold q, by simp only [Walk.length_cons]; omega⟩)
    · have ho : (u = x ∧ v = y) ∨ (u = y ∧ v = x) := by
        simpa only [Sym2.eq_iff] using he
      rcases ho with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact Or.inr (Or.inl ⟨.nil,by simp⟩)
      · exact Or.inr (Or.inr ⟨.nil,by simp⟩)

/-- A lower path-length bound is stable under a new edge if both of its
endpoints are sufficiently far from the starting vertex. -/
theorem length_lower_addEdge (N : ℕ)
    (hab : ∀ q : G.Walk a b, N ≤ q.length)
    (hax : ∀ q : G.Walk a x, N ≤ q.length + 1)
    (hay : ∀ q : G.Walk a y, N ≤ q.length + 1)
    (p : (addEdge G x y).Walk a b) : N ≤ p.length := by
  rcases first_new_edge p with ⟨q,hq⟩ | ⟨q,hq⟩ | ⟨q,hq⟩
  · exact (hab q).trans hq
  · exact (hax q).trans hq
  · exact (hay q).trans hq

/-- In a graph of girth at least L, an alternate path across an old edge
has length at least L-1. This is precisely the nonbad-edge input to the
matching transposition argument. -/
theorem girth_alternate_lower (L : ℕ) (hG : (L : ℕ∞) ≤ G.egirth)
    (hxy : G.Adj x y) (p : (G.deleteEdges {s(x,y)}).Walk x y) :
    L ≤ p.length + 1 := by
  classical
  let hp := p.mapLe (SimpleGraph.deleteEdges_le {s(x,y)})
  have he : s(x,y) ∉ hp.edges := by
    intro he
    have hmem : s(x,y) ∈ p.edges := by simpa only [hp,Walk.edges_mapLe_eq_edges] using he
    have hg := p.edges_subset_edgeSet hmem
    simp at hg
  have hc := hp.toPath.cons_isCycle hxy.symm (by
    rw [Sym2.eq_swap]
    exact fun h => he (Walk.edges_toPath_subset_edges hp h))
  have hh := SimpleGraph.le_egirth.mp hG y (.cons hxy.symm hp.toPath) hc
  have hlen := hp.length_bypass_le_length
  have hh' : L ≤ hp.bypass.length + 1 := by exact_mod_cast hh
  simpa only [hp,Walk.length_mapLe] using hh'.trans (Nat.add_le_add_right hlen 1)

/-- Two-switching in a simple graph: delete xy and uz, then add xz and uy.
The distance condition is the manuscript's separation of the two endpoint
sets. All previous prescribed edges survive provided neither deleted edge
was among those prescriptions. -/
theorem girth_switch (L : ℕ) {x y u z : V}
    (hG : (L : ℕ∞) ≤ G.egirth) (huz : G.Adj u z)
    (hfar : ∀ a ∈ ({x,y} : Set V), ∀ b ∈ ({u,z} : Set V),
      ∀ p : G.Walk a b, 2 * L < p.length) :
    (L : ℕ∞) ≤
      (addEdge (addEdge (G.deleteEdges {s(x,y),s(u,z)}) x z) u y).egirth := by
  let H := G.deleteEdges {s(x,y),s(u,z)}
  have hHG : H ≤ G := SimpleGraph.deleteEdges_le _
  have hH : (L : ℕ∞) ≤ H.egirth := hG.trans (SimpleGraph.egirth_anti hHG)
  have hxz (p : H.Walk x z) : L ≤ p.length + 1 := by
    have hf := hfar x (by simp) z (by simp) (p.mapLe hHG)
    simp only [Walk.length_mapLe] at hf
    omega
  have hg1 := girth_addEdge L hH hxz
  apply girth_addEdge L hg1
  intro p
  rcases first_new_edge p with ⟨q,hq⟩ | ⟨q,hq⟩ | ⟨q,hq⟩
  · have hf := hfar y (by simp) u (by simp) ((q.mapLe hHG).reverse)
    simp only [Walk.length_reverse,Walk.length_mapLe] at hf
    omega
  · have hf := hfar x (by simp) u (by simp) ((q.mapLe hHG).reverse)
    simp only [Walk.length_reverse,Walk.length_mapLe] at hf
    omega
  · have hdel : H ≤ G.deleteEdges {s(u,z)} := by
      apply SimpleGraph.deleteEdges_anti
      simp only [Set.singleton_subset_iff,Set.mem_insert_iff,Set.mem_singleton_iff]
      simp
    have hl := girth_alternate_lower L hG huz (q.mapLe hdel)
    simp only [Walk.length_mapLe] at hl
    omega

/-- Short cycles in an edge-adjoined graph descend to the old graph whenever
there is no short alternate path. This needs no girth assumption on the old
graph, and so also applies during the initial bad-edge repair algorithm. -/
theorem short_cycle_descends_add (L : ℕ)
    (hx : ∀ p : G.Walk x y, L ≤ p.length + 1)
    (p : (addEdge G x y).Walk a a) (hp : p.IsCycle) (hlen : p.length < L) :
    ∃ q : G.Walk a a, q.IsCycle ∧ q.edges = p.edges ∧ q.length = p.length := by
  classical
  have he : s(x,y) ∉ p.edges := by
    intro he
    obtain ⟨u,v,q,huv,hqe,hql⟩ := alternate_walk p hp.isTrail _ he
    obtain ⟨q',hq'⟩ := transfer_addEdge q hqe
    have ho : (u = x ∧ v = y) ∨ (u = y ∧ v = x) := by
      simpa only [Sym2.eq_iff] using huv
    have hl : L ≤ q'.length + 1 := by
      rcases ho with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hx q'
      · simpa only [Walk.length_reverse] using hx q'.reverse
    omega
  have ht : ∀ e, e ∈ p.edges → e ∈ G.edgeSet := by
    intro e he'
    have hg := p.edges_subset_edgeSet he'
    simp only [addEdge, SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_fromEdgeSet,
      Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff] at hg
    rcases hg with hg | ⟨rfl,_⟩
    · exact hg
    · exact False.elim (he he')
  exact ⟨p.transfer G ht,hp.transfer ht,Walk.edges_transfer ..,Walk.length_transfer ..⟩

/-- Local nonbadness of one edge suffices for the alternate-path estimate. -/
theorem nonbad_alternate_lower (L : ℕ) (hxy : G.Adj x y)
    (hnonbad : ∀ a (c : G.Walk a a), c.IsCycle → c.length < L → s(x,y) ∉ c.edges)
    (p : (G.deleteEdges {s(x,y)}).Walk x y) : L ≤ p.length + 1 := by
  classical
  let hp := p.mapLe (SimpleGraph.deleteEdges_le {s(x,y)})
  have he : s(x,y) ∉ hp.edges := by
    intro he
    have hmem : s(x,y) ∈ p.edges := by simpa only [hp,Walk.edges_mapLe_eq_edges] using he
    have hg := p.edges_subset_edgeSet hmem
    simp at hg
  have hc := hp.toPath.cons_isCycle hxy.symm (by
    rw [Sym2.eq_swap]
    exact fun h => he (Walk.edges_toPath_subset_edges hp h))
  by_contra hl
  have hlen : (Walk.cons hxy.symm (hp.toPath : G.Walk x y)).length < L := by
    have hh := hp.length_bypass_le_length
    simp only [Walk.length_cons]
    change hp.bypass.length + 1 < L
    have hhp : hp.length = p.length := Walk.length_mapLe _ _
    omega
  apply hnonbad y _ hc hlen
  simp only [Walk.edges_cons,List.mem_cons]
  exact Or.inl (Sym2.eq_swap)

/-- The repair two-switch creates no short cycle, even before girth has been
repaired everywhere. Deleting a bad edge therefore strictly reduces the bad
edge set; this local assertion is the core of the repair argument. -/
theorem short_cycle_descends_switch (L : ℕ) {x y u z : V}
    (huz : G.Adj u z)
    (hnonbad : ∀ a (c : G.Walk a a), c.IsCycle → c.length < L → s(u,z) ∉ c.edges)
    (hfar : ∀ a ∈ ({x,y} : Set V), ∀ b ∈ ({u,z} : Set V),
      ∀ p : G.Walk a b, 2 * L < p.length)
    (p : (addEdge (addEdge (G.deleteEdges {s(x,y),s(u,z)}) x z) u y).Walk a a)
    (hp : p.IsCycle) (hlen : p.length < L) :
    ∃ q : (G.deleteEdges {s(x,y),s(u,z)}).Walk a a,
      q.IsCycle ∧ q.edges = p.edges ∧ q.length = p.length := by
  let H := G.deleteEdges {s(x,y),s(u,z)}
  have hHG : H ≤ G := SimpleGraph.deleteEdges_le _
  have hxz (p : H.Walk x z) : L ≤ p.length + 1 := by
    have hf := hfar x (by simp) z (by simp) (p.mapLe hHG)
    simp only [Walk.length_mapLe] at hf
    omega
  have huy (p : (addEdge H x z).Walk u y) : L ≤ p.length + 1 := by
    rcases first_new_edge p with ⟨q,hq⟩ | ⟨q,hq⟩ | ⟨q,hq⟩
    · have hf := hfar y (by simp) u (by simp) ((q.mapLe hHG).reverse)
      simp only [Walk.length_reverse,Walk.length_mapLe] at hf
      omega
    · have hf := hfar x (by simp) u (by simp) ((q.mapLe hHG).reverse)
      simp only [Walk.length_reverse,Walk.length_mapLe] at hf
      omega
    · have hdel : H ≤ G.deleteEdges {s(u,z)} := by
        apply SimpleGraph.deleteEdges_anti
        simp
      have hl := nonbad_alternate_lower L huz hnonbad (q.mapLe hdel)
      simp only [Walk.length_mapLe] at hl
      omega
  obtain ⟨q,hq,hqe,hql⟩ := short_cycle_descends_add L huy p hp hlen
  obtain ⟨q',hq',hq'e,hq'l⟩ := short_cycle_descends_add L hxz q hq (by omega)
  exact ⟨q',hq',hq'e.trans hqe,hq'l.trans hql⟩

/-- At the shortest-cycle threshold, no nonbadness requirement is needed
on the auxiliary edge: a new cycle using both new edges is strictly longer
than the old girth. This permits deterministic girth repair. -/
theorem shortest_cycle_descends_switch (L : ℕ) {x y u z : V}
    (hG : (L : ℕ∞) ≤ G.egirth) (huz : G.Adj u z)
    (hfar : ∀ a ∈ ({x,y} : Set V), ∀ b ∈ ({u,z} : Set V),
      ∀ p : G.Walk a b, 2 * (L+1) < p.length)
    (p : (addEdge (addEdge (G.deleteEdges {s(x,y),s(u,z)}) x z) u y).Walk a a)
    (hp : p.IsCycle) (hlen : p.length < L+1) :
    ∃ q : (G.deleteEdges {s(x,y),s(u,z)}).Walk a a,
      q.IsCycle ∧ q.edges = p.edges ∧ q.length = p.length := by
  let H := G.deleteEdges {s(x,y),s(u,z)}
  have hHG : H ≤ G := SimpleGraph.deleteEdges_le _
  have hxz (p : H.Walk x z) : L+1 ≤ p.length + 1 := by
    have hf := hfar x (by simp) z (by simp) (p.mapLe hHG)
    simp only [Walk.length_mapLe] at hf
    omega
  have huy (p : (addEdge H x z).Walk u y) : L+1 ≤ p.length + 1 := by
    rcases first_new_edge p with ⟨q,hq⟩ | ⟨q,hq⟩ | ⟨q,hq⟩
    · have hf := hfar y (by simp) u (by simp) ((q.mapLe hHG).reverse)
      simp only [Walk.length_reverse,Walk.length_mapLe] at hf
      omega
    · have hf := hfar x (by simp) u (by simp) ((q.mapLe hHG).reverse)
      simp only [Walk.length_reverse,Walk.length_mapLe] at hf
      omega
    · have hdel : H ≤ G.deleteEdges {s(u,z)} := by
        apply SimpleGraph.deleteEdges_anti
        simp
      have hl := girth_alternate_lower L hG huz (q.mapLe hdel)
      simp only [Walk.length_mapLe] at hl
      omega
  obtain ⟨q,hq,hqe,hql⟩ := short_cycle_descends_add (L+1) huy p hp hlen
  obtain ⟨q',hq',hq'e,hq'l⟩ := short_cycle_descends_add (L+1) hxz q hq (by omega)
  exact ⟨q',hq',hq'e.trans hqe,hq'l.trans hql⟩

/-- The exact set minimized by the finite repair argument. -/
def badEdges (G : SimpleGraph V) (L : ℕ) : Set (Sym2 V) :=
  {e | ∃ (a : V) (p : G.Walk a a), p.IsCycle ∧ p.length < L ∧ e ∈ p.edges}

theorem badEdges_subset {L : ℕ} : badEdges G L ⊆ G.edgeSet := by
  rintro e ⟨a,p,hp,hl,he⟩
  exact p.edges_subset_edgeSet he

/-- Edgewise transfer of short cycles strictly reduces the bad edge set
as soon as a specified old bad edge has been deleted. -/
theorem badEdges_strict {L : ℕ} [Fintype V] (e : Sym2 V) (he : e ∈ badEdges G L)
    (hdesc : ∀ a (p : H.Walk a a), p.IsCycle → p.length < L →
      ∃ q : G.Walk a a, q.IsCycle ∧ q.edges = p.edges ∧ q.length = p.length)
    (hdel : e ∉ badEdges H L) :
    (badEdges H L).toFinite.toFinset.card < (badEdges G L).toFinite.toFinset.card := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_,?_⟩
  · intro f hf
    have hf' : f ∈ badEdges H L := by simpa using hf
    obtain ⟨a,p,hp,hl,hf'⟩ := hf'
    obtain ⟨q,hq,hqe,hql⟩ := hdesc a p hp hl
    simpa using (show f ∈ badEdges G L from ⟨a,q,hq,by omega,hqe ▸ hf'⟩)
  · intro heq
    have heH : e ∈ (badEdges H L).toFinite.toFinset := by
      rw [heq]
      simpa using he
    have heH' : e ∈ badEdges H L := by simpa using heH
    exact hdel heH'

/-- Finite extremal repair raises the girth by one. Unlike the manuscript's
probabilistic initialization, this argument only needs the uniform far-edge
supply; all objects and the final girth condition are unchanged. -/
theorem girth_improve_one [Fintype V] (L : ℕ) (P : SimpleGraph V → Prop)
    (hne : ∃ G, P G ∧ (L : ℕ∞) ≤ G.egirth)
    (hswitch : ∀ G, P G → ∀ a (p : G.Walk a a), p.IsCycle →
      ∃ x y u z, s(x,y) ∈ p.edges ∧ G.Adj u z ∧
        (∀ a ∈ ({x,y} : Set V), ∀ b ∈ ({u,z} : Set V),
          ∀ p : G.Walk a b, 2 * (L+1) < p.length) ∧
        P (addEdge (addEdge (G.deleteEdges {s(x,y),s(u,z)}) x z) u y)) :
    ∃ G, P G ∧ ((L+1 : ℕ) : ℕ∞) ≤ G.egirth := by
  classical
  let S : Set (SimpleGraph V) := {G | P G ∧ (L : ℕ∞) ≤ G.egirth}
  obtain ⟨G,hGP,hmin⟩ := S.exists_min_image
    (fun G => (badEdges G (L+1)).toFinite.toFinset.card) S.toFinite hne
  refine ⟨G,hGP.1,?_⟩
  by_contra hn
  rw [SimpleGraph.le_egirth] at hn
  push Not at hn
  obtain ⟨a,p,hp,hl⟩ := hn
  have hlen : p.length < L+1 := by exact_mod_cast hl
  obtain ⟨x,y,u,z,he,huz,hfar,hP⟩ := hswitch G hGP.1 a p hp
  let e := s(x,y)
  let H := addEdge (addEdge (G.deleteEdges {s(x,y),s(u,z)}) x z) u y
  have hdesc (a : V) (q : H.Walk a a) (hq : q.IsCycle) (hl : q.length < L+1) :=
    shortest_cycle_descends_switch L hGP.2 huz hfar q hq hl
  have hstrict : (badEdges H (L+1)).toFinite.toFinset.card <
      (badEdges G (L+1)).toFinite.toFinset.card := by
    apply badEdges_strict e ⟨a,p,hp,hlen,he⟩
    · intro a q hq hl
      obtain ⟨q',hq',hqe,hql⟩ := hdesc a q hq hl
      exact ⟨q'.mapLe (SimpleGraph.deleteEdges_le _), hq'.mapLe _,
        (Walk.edges_mapLe_eq_edges ..).trans hqe,(Walk.length_mapLe ..).trans hql⟩
    · rintro ⟨a,q,hq,hl,heq⟩
      obtain ⟨q',hq',hqe,hql⟩ := hdesc a q hq hl
      have hg := q'.edges_subset_edgeSet (hqe ▸ heq)
      change s(x,y) ∈ (G.deleteEdges {s(x,y),s(u,z)}).edgeSet at hg
      simp at hg
  have hHg : (L : ℕ∞) ≤ H.egirth := girth_switch L hGP.2 huz (by
    intro a ha b hb q
    have hh := hfar a ha b hb q
    omega)
  exact (not_lt_of_ge (hmin H ⟨hP,hHg⟩)) hstrict

/-- Arbitrarily specified finite girth follows by finitely many exact
transpositions if the family has a uniform distant auxiliary edge supply. -/
theorem exists_large_girth [Fintype V] (N : ℕ) (P : SimpleGraph V → Prop)
    (hne : ∃ G, P G)
    (hswitch : ∀ G, P G → ∀ a (p : G.Walk a a), p.IsCycle →
      ∃ x y u z, s(x,y) ∈ p.edges ∧ G.Adj u z ∧
        (∀ a ∈ ({x,y} : Set V), ∀ b ∈ ({u,z} : Set V),
          ∀ p : G.Walk a b, 2 * N < p.length) ∧
        P (addEdge (addEdge (G.deleteEdges {s(x,y),s(u,z)}) x z) u y)) :
    ∃ G, P G ∧ (N : ℕ∞) ≤ G.egirth := by
  have hstep : ∀ k ≤ N, ∃ G, P G ∧ (k : ℕ∞) ≤ G.egirth := by
    intro k
    induction k with
    | zero =>
      intro _
      obtain ⟨G,hG⟩ := hne
      exact ⟨G,hG,zero_le⟩
    | succ k ih =>
      intro hk
      apply girth_improve_one k P (ih (by omega))
      intro G hG a p hp
      obtain ⟨x,y,u,z,he,huz,hfar,hP⟩ := hswitch G hG a p hp
      refine ⟨x,y,u,z,he,huz,?_,hP⟩
      intro a ha b hb p
      have hf := hfar a ha b hb p
      omega
  exact hstep N le_rfl

/-- Below the girth, a nonbacktracking walk cannot repeat a vertex.
This is the quantitative version of Mathlib's forest lemma. -/
theorem short_reduced_isPath (L : ℕ) (hG : L ≤ G.egirth)
    (p : G.Walk a b) (hlen : p.length < L)
    (h : p.edges.IsChain (· ≠ ·)) : p.IsPath := by
  classical
  induction p with
  | nil => simp
  | @cons u v w head tail ih =>
    have hcc := List.isChain_cons.mp (Walk.edges_cons _ _ ▸ h)
    have hi : tail.IsPath := ih (by simpa only [Walk.length_cons] using
      (show tail.length + 1 < L from hlen) |> fun h => by omega) hcc.2
    refine Walk.cons_isPath_iff head tail |>.mpr ⟨hi, ?_⟩
    rcases tail.length.eq_zero_or_pos with hz | hz
    · simp [Walk.nil_iff_support_eq.mp (Walk.length_eq_zero_iff.mp hz), head.ne]
    · by_contra hh
      have hc : (Walk.cons head (tail.takeUntil u hh)).IsCycle := by
        simp only [Walk.isCycle_def, Walk.isTrail_def, Walk.edges_cons, List.nodup_cons,
          ne_eq, reduceCtorEq, not_false_eq_true, Walk.support_cons, List.tail_cons, true_and]
        have ht : (Walk.cons head (tail.takeUntil u hh)).support.tail.Nodup :=
          tail.isPath_def.mp hi |>.sublist <| List.IsInfix.sublist
            ⟨[], (tail.dropUntil u hh).support.tail, by simp [← Walk.support_append]⟩
        refine ⟨⟨?_, Walk.edges_nodup_of_support_nodup ht⟩, ht⟩
        by_contra he
        refine hcc.1 s(u,v) ?_ rfl
        rw [← tail.cons_tail_eq (by simp [Walk.not_nil_iff_lt_length, hz])]
        have hh' := Walk.IsPath.mk' ht |>.eq_snd_of_mem_edges (Sym2.eq_swap ▸ he)
        simp [hh', Walk.snd_takeUntil head.ne]
      have hg := hc.egirth_le_length
      have ht := tail.length_takeUntil_le_length hh
      have hn : L ≤ (Walk.cons head (tail.takeUntil u hh)).length :=
        ENat.natCast_le_natCast.mp (hG.trans hg)
      simp only [Walk.length_cons] at hn hlen
      omega

/-- Every nonempty immersed circuit has at least the graph's girth. -/
theorem reduced_closed_length (L : ℕ) (hG : L ≤ G.egirth)
    (p : G.Walk a a) (hne : 0 < p.length)
    (h : p.edges.IsChain (· ≠ ·)) : L ≤ p.length := by
  by_contra hn
  have hp := short_reduced_isPath L hG p (by omega) h
  have he := (Walk.isPath_iff_nil.mp hp).eq_nil
  have hl : p.length = 0 := by rw [he]; rfl
  omega

end TorsionFreeZeroDivisors.GirthSwitch

/-! ### Typed matching families have nonempty large-girth spaces. -/

end

end OAI
