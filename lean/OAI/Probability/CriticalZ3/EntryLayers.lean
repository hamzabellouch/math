import OAI.Probability.CriticalZ3.LatticePaths

namespace OAI

open MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open Classical

theorem step_ge (x : Vertex) (i : Fin 3) : x ≤ step x i := by
  intro j; simp only [step]; split_ifs <;> omega

theorem step_direction_injective (x : Vertex) : Function.Injective (step x) := by
  intro i j h
  by_contra hij
  have hh := congrFun h i
  simp only [step,ite_true,ite_eq_right (Ne.symm hij),add_zero] at hh
  omega

theorem step_no_reverse (x y : Vertex) (i j : Fin 3)
    (h : y = step x i) : x ≠ step y j := by
  intro hh
  have hle : y i ≤ x i := by rw [hh]; exact step_ge y j i
  have hlt : x i < y i := by simp [h,step]
  exact not_lt_of_ge hle hlt

theorem incidence_unique {e f : Bond} {x y : Vertex}
    (he : Incidence e x y) (hf : Incidence f x y) : e = f := by
  rcases he with ⟨hx,hy⟩ | ⟨hy,hx⟩ <;> rcases hf with ⟨hx',hy'⟩ | ⟨hy',hx'⟩
  · apply Prod.ext
    · exact hx.symm.trans hx'
    · apply step_direction_injective x
      simpa only [←hx,←hx'] using hy.symm.trans hy'
  · exact False.elim (step_no_reverse x y e.2 f.2 (by simpa [←hx] using hy)
      (by simpa [←hy'] using hx'))
  · exact False.elim (step_no_reverse y x e.2 f.2 (by simpa [←hy] using hx)
      (by simpa [←hx'] using hy'))
  · apply Prod.ext
    · exact hy.symm.trans hy'
    · apply step_direction_injective y
      simpa only [←hy,←hy'] using hx.symm.trans hx'

noncomputable def neighborBond (x y : Vertex) : Bond :=
  if h : NearestNeighbor x y then (LatticeGraph.neighbor_incidence h).choose else (x,0)

theorem neighborBond_incidence {x y : Vertex} (h : NearestNeighbor x y) :
    Incidence (neighborBond x y) x y := by
  simp only [neighborBond,dite_eq_left h]
  exact (LatticeGraph.neighbor_incidence h).choose_spec

theorem neighborBond_eq {e : Bond} {x y : Vertex} (he : Incidence e x y) :
    neighborBond x y = e := incidence_unique (neighborBond_incidence (incidence_neighbor he)) he

namespace Box

def Exterior (C : Box) (y : Vertex) : Prop :=
  ¬C.Contains y ∧ ∃ z, C.Contains z ∧ NearestNeighbor y z

noncomputable def entry (C : Box) (y : Vertex) : Vertex :=
  if h : C.Exterior y then h.2.choose else C.lower

theorem entry_spec {C : Box} {y : Vertex} (h : C.Exterior y) :
    C.Contains (C.entry y) ∧ NearestNeighbor y (C.entry y) := by
  simp only [entry,dite_eq_left h]
  exact h.2.choose_spec

theorem entry_eq {C : Box} {y z : Vertex} (hy : ¬C.Contains y)
    (hz : C.Contains z) (h : NearestNeighbor y z) : C.entry y = z := by
  have hey : C.Exterior y := ⟨hy,z,hz,h⟩
  exact C.exterior_neighbor_unique hy (entry_spec hey).1 hz (entry_spec hey).2 h

noncomputable def entryBit (C : Box) : (m : Model) → Vertex → m.Bit
  | .bond,y => neighborBond y (C.entry y)
  | .site,y => C.entry y

theorem exterior_expand {C : Box} {y : Vertex} (h : C.Exterior y) :
    (C.expand 1).Contains y := by
  obtain ⟨z,hz,hzy⟩ := h.2
  apply C.neighbor_in_expand hz
  obtain ⟨i,hi | hi⟩ := hzy
  · exact ⟨i,Or.inr hi⟩
  · exact ⟨i,Or.inl hi⟩

theorem entryBit_internal (m : Model) {C : Box} {y : Vertex} (h : C.Exterior y) :
    C.entryBit m y ∈ (C.expand 1).bits m := by
  have he := C.contains_expand 1 (entry_spec h).1
  cases m
  · exact LatticeGraph.incidence_internal (exterior_expand h) he
      (neighborBond_incidence (entry_spec h).2)
  · exact (mem_vertices _ _).mpr he

end Box

namespace LatticeGraph
variable (G : LatticeGraph)

def OutsideAdj (m : Model) (C : Box) (ω : m.Config) (x y : G.Node) : Prop :=
  ¬C.Contains x.1 ∧ ¬C.Contains y.1 ∧ G.Adj m ω x y

def OutsideReach (m : Model) (C : Box) (ω : m.Config) (o y : G.Node) : Prop :=
  ¬C.Contains o.1 ∧ G.Open m ω o ∧ Relation.ReflTransGen (G.OutsideAdj m C ω) o y

noncomputable def entrants (m : Model) (C : Box) (ω : m.Config) (o : G.Node) : Finset Vertex :=
  G.vertices.filter (fun y => ∃ hy : y ∈ G.vertices,
    C.Exterior y ∧ G.OutsideReach m C ω o ⟨y,hy⟩)

@[simp] theorem mem_entrants (m : Model) (C : Box) (ω : m.Config) (o y : G.Node) :
    y.1 ∈ G.entrants m C ω o ↔ C.Exterior y.1 ∧ G.OutsideReach m C ω o y := by
  simp only [entrants,Finset.mem_filter,y.2,true_and]
  exact ⟨fun ⟨_,h⟩ => h,fun h => ⟨trivial,h⟩⟩

theorem outsideReach_conn (m : Model) {C : Box} {ω : m.Config} {o y : G.Node}
    (h : G.OutsideReach m C ω o y) : G.Conn m ω o y :=
  (G.conn_iff m ω o y).mpr ⟨h.2.1,Relation.ReflTransGen.mono (fun _ _ (hh : G.OutsideAdj m C ω _ _) => hh.2.2) o y h.2.2⟩

theorem first_entry (m : Model) {C : Box} {ω : m.Config} {o z : G.Node}
    (ho : ¬C.Contains o.1) (hz : C.Contains z.1) (h : G.Conn m ω o z) :
    ∃ y w : G.Node, y.1 ∈ G.entrants m C ω o ∧ C.Contains w.1 ∧ G.Adj m ω y w := by
  have hp := ((G.conn_iff m ω o z).mp h).2
  have hop := ((G.conn_iff m ω o z).mp h).1
  have hh : ∀ {x : G.Node}, Relation.ReflTransGen (G.Adj m ω) o x →
      (¬C.Contains x.1 ∧ Relation.ReflTransGen (G.OutsideAdj m C ω) o x) ∨
      ∃ y w : G.Node, y.1 ∈ G.entrants m C ω o ∧ C.Contains w.1 ∧ G.Adj m ω y w := by
    intro x hx
    induction hx with
    | refl => exact Or.inl ⟨ho,.refl⟩
    | @tail a b _ hab ih =>
      rcases ih with ⟨ha,hi⟩ | he
      · by_cases hb : C.Contains b.1
        · exact Or.inr ⟨a,b,(G.mem_entrants m C ω o a).mpr
            ⟨⟨ha,b.1,hb,G.adj_neighbor m hab⟩,ho,hop,hi⟩,hb,hab⟩
        · exact Or.inl ⟨hb,hi.tail ⟨ha,hb,hab⟩⟩
      · exact Or.inr he
  exact (hh hp).resolve_left (fun h => h.1 hz)

theorem meets_entrants_nonempty (m : Model) {C : Box} {ω : m.Config} {o : G.Node}
    (ho : ¬C.Contains o.1) (h : G.Meets m ω o {x | C.Contains x}) :
    (G.entrants m C ω o).Nonempty := by
  obtain ⟨z,hz,hz'⟩ := h
  obtain ⟨y,w,hy,_,_⟩ := G.first_entry m ho hz hz'
  exact ⟨y.1,hy⟩

theorem entryBit_open (m : Model) {C : Box} {ω : m.Config} {y z : G.Node}
    (hy : ¬C.Contains y.1) (hz : C.Contains z.1) (h : G.Adj m ω y z) :
    ω (C.entryBit m y.1) = true := by
  have he := C.entry_eq hy hz (G.adj_neighbor m h)
  cases m
  · obtain ⟨e,_,hi,ho⟩ := h
    simpa only [Box.entryBit,he,neighborBond_eq hi] using ho
  · simpa only [Box.entryBit,he] using h.2.2

noncomputable def entryBits (m : Model) (C : Box) (ω : m.Config) (o : G.Node) : Finset m.Bit :=
  (G.entrants m C ω o).image (C.entryBit m)

def Blocked (m : Model) (C : Box) (ω : m.Config) (o : G.Node) : Prop :=
  ∀ e ∈ G.entryBits m C ω o, ω e = false

theorem entryBits_card (m : Model) (C : Box) (ω : m.Config) (o : G.Node) :
    (G.entryBits m C ω o).card ≤ (G.entrants m C ω o).card := Finset.card_image_le

theorem blocked_not_meets (m : Model) {C : Box} {ω : m.Config} {o : G.Node}
    (ho : ¬C.Contains o.1) (hb : G.Blocked m C ω o) :
    ¬G.Meets m ω o {x | C.Contains x} := by
  rintro ⟨z,hz,hp⟩
  obtain ⟨y,w,hy,hw,hyw⟩ := G.first_entry m ho hz hp
  have hyout := ((G.mem_entrants m C ω o y).mp hy).1.1
  have hopen := G.entryBit_open m hyout hw hyw
  have hclosed := hb (C.entryBit m y.1) (Finset.mem_image.mpr ⟨y.1,hy,rfl⟩)
  exact Bool.noConfusion (hopen.symm.trans hclosed)

/-- The shell blocking events are disjoint for the actual induced-outside
paths. This is the pathwise argument, not a probabilistic assumption. -/
theorem blocked_earlier_entrants (m : Model) {B : Box} {i j : ℕ} (hij : i < j)
    {ω : m.Config} {o : G.Node} (ho : ¬(B.expand j).Contains o.1)
    (hb : G.Blocked m (B.expand j) ω o) : G.entrants m (B.expand i) ω o = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro y hy
  have hyG : y ∈ G.vertices := (Finset.mem_filter.mp hy).1
  obtain ⟨hey,hry⟩ := (G.mem_entrants m (B.expand i) ω o ⟨y,hyG⟩).mp hy
  have hyj : (B.expand j).Contains y := by
    have he := Box.exterior_expand hey
    rw [Box.expand_expand] at he
    exact B.expand_mono (by omega) he
  exact G.blocked_not_meets m ho hb ⟨⟨y,hyG⟩,hyj,G.outsideReach_conn m hry⟩

end LatticeGraph
end CriticalZ3

namespace CriticalZ3.LatticeGraph
open Classical
variable (G : LatticeGraph)

noncomputable def outsideBits : (m : Model) → Box → Finset m.Bit
  | .bond,C => G.edges.filter (fun e => ¬C.Contains e.1 ∧ ¬C.Contains (step e.1 e.2))
  | .site,C => G.vertices.filter (fun x => ¬C.Contains x)

theorem outsideAdj_determined (m : Model) (C : Box) (ω ω' : m.Config)
    (h : ∀ e ∈ G.outsideBits m C, ω' e = ω e) (x y : G.Node) :
    G.OutsideAdj m C ω' x y ↔ G.OutsideAdj m C ω x y := by
  have hh (ω ω' : m.Config) (h : ∀ e ∈ G.outsideBits m C, ω' e = ω e)
      (ha : G.OutsideAdj m C ω' x y) : G.OutsideAdj m C ω x y := by
    refine ⟨ha.1,ha.2.1,?_⟩
    cases m
    · obtain ⟨e,he,hi,ho⟩ := ha.2.2
      refine ⟨e,he,hi,?_⟩
      have hem : e ∈ G.outsideBits .bond C := by
        apply Finset.mem_filter.mpr
        refine ⟨he,?_⟩
        rcases hi with ⟨hx,hy⟩ | ⟨hy,hx⟩
        · exact ⟨hx ▸ ha.1,hy ▸ ha.2.1⟩
        · exact ⟨hy ▸ ha.2.1,hx ▸ ha.1⟩
      rw [←h e hem]; exact ho
    · exact ⟨ha.2.2.1,(h x.1 (Finset.mem_filter.mpr ⟨x.2,ha.1⟩)) ▸ ha.2.2.2.1,
        (h y.1 (Finset.mem_filter.mpr ⟨y.2,ha.2.1⟩)) ▸ ha.2.2.2.2⟩
  exact ⟨hh ω ω' h, hh ω' ω (fun e he => (h e he).symm)⟩

theorem outsideReach_determined (m : Model) (C : Box) (ω ω' : m.Config)
    (h : ∀ e ∈ G.outsideBits m C, ω' e = ω e) (o y : G.Node) :
    G.OutsideReach m C ω' o y ↔ G.OutsideReach m C ω o y := by
  by_cases ho : C.Contains o.1
  · simp only [OutsideReach,ho,not_true_eq_false,false_and]
  have hr : G.OutsideAdj m C ω' = G.OutsideAdj m C ω := by
    funext x y; exact propext (G.outsideAdj_determined m C ω ω' h x y)
  have hop : G.Open m ω' o ↔ G.Open m ω o := by
    cases m
    · rfl
    · change (ω' o.1 = true) ↔ (ω o.1 = true)
      rw [h o.1 (Finset.mem_filter.mpr ⟨o.2,ho⟩)]
  simp only [OutsideReach,hr,hop]

theorem entrants_determined (m : Model) (C : Box) (o : G.Node) :
    ProductCylinder.DeterminedBy (G.outsideBits m C) (fun ω => G.entrants m C ω o) := by
  intro ω ω' h
  ext y
  simp only [entrants,Finset.mem_filter,G.outsideReach_determined m C ω ω' h]

theorem entryBits_determined (m : Model) (C : Box) (o : G.Node) :
    ProductCylinder.DeterminedBy (G.outsideBits m C) (fun ω => G.entryBits m C ω o) := by
  intro ω ω' h
  simp only [entryBits,G.entrants_determined m C o ω ω' h]

theorem outsideBits_disjoint_inside (m : Model) (C : Box) :
    Disjoint (G.outsideBits m C) (C.bits m) := by
  rw [Finset.disjoint_left]
  intro e he he'
  cases m
  · exact (Finset.mem_filter.mp he).2.1 ((Box.mem_bonds C e).mp he').1
  · exact (Finset.mem_filter.mp he).2 ((Box.mem_vertices C e).mp he')

theorem entryBit_not_outside (m : Model) {C : Box} {y : Vertex} (hy : C.Exterior y) :
    C.entryBit m y ∉ G.outsideBits m C := by
  intro he
  have hentry := (Box.entry_spec hy).1
  cases m
  · have hi := neighborBond_incidence (Box.entry_spec hy).2
    obtain ⟨_,hout,hout'⟩ := Finset.mem_filter.mp he
    rcases hi with ⟨_,hz⟩ | ⟨hz,_⟩
    · exact hout' (hz ▸ hentry)
    · exact hout (hz ▸ hentry)
  · exact (Finset.mem_filter.mp he).2 hentry

theorem entryBits_disjoint_outside (m : Model) (C : Box) (ω : m.Config) (o : G.Node) :
    Disjoint (G.entryBits m C ω o) (G.outsideBits m C) := by
  rw [Finset.disjoint_left]
  intro e he he'
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp he
  have hyG : y ∈ G.vertices := (Finset.mem_filter.mp hy).1
  exact G.entryBit_not_outside m ((G.mem_entrants m C ω o ⟨y,hyG⟩).mp hy).1 he'

end CriticalZ3.LatticeGraph

end OAI
