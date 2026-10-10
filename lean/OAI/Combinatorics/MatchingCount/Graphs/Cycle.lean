import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.ChosenChord

namespace OAI

namespace MatchingFPRAS.Transport.CellDemands
variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]
variable {bags : V → Finset L}
variable {G : SimpleGraph L}
variable (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)
variable (hG : G.IsAcyclic)
namespace Demand

variable {hbags hG} (d : Demand hbags hG)

noncomputable def cycle := d.2.1.cycle

omit [Fintype L] in
lemma cell : (d.cycle.labelCycle hbags).Cell d.2.2.val.x d.2.2.val.p d.2.2.val.q d.2.2.val.y :=
  ((d.2.1.cycle.subdivision hbags hG).mem_cellList (List.mem_toFinset.mp d.2.2.property)).2.2

omit [Fintype L] in
lemma last_lt : d.2.2.val.y < d.cycle.size := by
  have hy := ((d.2.1.cycle.subdivision hbags hG).mem_cellList (List.mem_toFinset.mp d.2.2.property)).2.1
  have hsize := d.cycle.four_le
  change d.2.2.val.y ≤ d.cycle.size-1 at hy
  omega

noncomputable def corners : d.cycle.Corners := d.cycle.cellCorners hbags d.cell d.last_lt

noncomputable def raw (flags : Fin 64) : RawDemand (BagEdge.Incident (bags := bags)) :=
  d.corners.rawDemand d.1.1 d.1.2 flags

omit [Fintype L] in
theorem raw_injective (flags : Fin 64) : Function.Injective (fun d : Demand hbags hG => d.raw flags) := by
  intro d e h
  obtain ⟨p,S,a⟩ := d
  obtain ⟨q,T,b⟩ := e
  have heq : p = q := by
    apply Prod.ext
    · exact congrArg RawDemand.first h
    · exact congrArg RawDemand.second h
  subst q
  have hanc : S.cycle.edgeAt 0 = T.cycle.edgeAt 0 := congrArg RawDemand.anchor h
  have hST : S = T := S.anchor_recovers hanc
  subst T
  have hcorn := congrArg RawDemand.corners h
  have ha := ((S.cycle.subdivision hbags hG).mem_cellList (List.mem_toFinset.mp a.property))
  have hb := ((S.cycle.subdivision hbags hG).mem_cellList (List.mem_toFinset.mp b.property))
  have hsize := S.cycle.four_le
  have hax := ha.2.2.first_pos
  have hap := ha.2.2.middle_pos
  have haq := ha.2.2.third_pos
  have hbx := hb.2.2.first_pos
  have hbp := hb.2.2.middle_pos
  have hbq := hb.2.2.third_pos
  have hidx (i : Fin 4) := congrFun hcorn i
  have hpos : 0 < S.cycle.size := by omega
  have hinj {i j : ℕ} (hi : i < S.cycle.size) (hj : j < S.cycle.size)
      (hh : S.cycle.vertexAt i = S.cycle.vertexAt j) : i = j :=
    (S.cycle.vertexAt_eq_iff hpos ⟨by omega,by omega⟩ ⟨by omega,by omega⟩).mp hh
  have hab : a = b := by
    apply Subtype.ext
    apply MatchingFPRAS.Cells.CycleData.CellIndex.ext
    · apply hinj (by omega) (by omega)
      exact hidx 0
    · apply hinj (by omega) (by omega)
      exact hidx 1
    · apply hinj (by omega) (by omega)
      exact hidx 2
    · apply hinj (by omega) (by omega)
      exact hidx 3
  subst b
  rfl

end Demand

end MatchingFPRAS.Transport.CellDemands

namespace MatchingFPRAS.Transport

variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]

variable {inc : E → V → Prop}

omit [Fintype V] [DecidableEq V] in
lemma OddPath.closed_eq_through_of_short (p : OddPath inc) (chord : E)
    (hl : p.length = 1) (he : chord = p.edge 0) : p.closed chord = p.through := by
  simp [OddPath.closed,OddPath.through,OddPath.interior,pathPattern,hl,he,Finset.filter_singleton]

end MatchingFPRAS.Transport

namespace MatchingFPRAS.Transport.IndexedCycle

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L} (c : IndexedCycle (BagEdge.Incident (bags := bags)))

variable {G : SimpleGraph L}

variable (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)

omit [Fintype V] [Fintype L] in
lemma cellShort_chord {x p q y : ℕ} (hc : (c.labelCycle hbags).Cell x p q y)
    (hy : y < c.size) (i : Fin 4) (hl : ((c.pathsOfCell hbags hc hy).side i).length = 1) :
    (c.pathsOfCell hbags hc hy).chord i = ((c.pathsOfCell hbags hc hy).side i).edge 0 := by
  have hxp := hc.first_pos
  have hpq := hc.middle_pos
  have hqy := hc.third_pos
  change (c.cellChords hbags hc hy) i = ((c.cellCorners hbags hc hy).side i).edge 0
  change (c.cellCorners hbags hc hy).length i = 1 at hl
  fin_cases i
  · simp only [Corners.length,Corners.start,Corners.stop,cellCorners] at hl
    have h : p = x+1 := by simp at hl; omega
    simpa [cellChords,Corners.side,arc,Corners.start,cellCorners] using c.chord_short hbags x p _ _ hc.first h
  · simp only [Corners.length,Corners.start,Corners.stop,cellCorners] at hl
    have h : q = p+1 := by simp at hl; omega
    simpa [cellChords,Corners.side,arc,Corners.start,cellCorners] using c.chord_short hbags p q _ _ hc.middle h
  · simp only [Corners.length,Corners.start,Corners.stop,cellCorners] at hl
    have h : y = q+1 := by simp at hl; omega
    simpa [cellChords,Corners.side,arc,Corners.start,cellCorners] using c.chord_short hbags q y _ _ hc.third h
  · simp only [Corners.length,Corners.start,Corners.stop,cellCorners] at hl
    have h : x = 0 ∧ y+1=c.size := by simp at hl; omega
    simpa [cellChords,Corners.side,arc,Corners.start,cellCorners] using c.chord_wrap hbags x y _ _ _ h

omit [Fintype V] [Fintype L] in
lemma cellShort_pattern {x p q y : ℕ} (hc : (c.labelCycle hbags).Cell x p q y)
    (hy : y < c.size) (i : Fin 4) (hl : ((c.pathsOfCell hbags hc hy).side i).length = 1) :
    ((c.pathsOfCell hbags hc hy).side i).closed ((c.pathsOfCell hbags hc hy).chord i) =
      ((c.pathsOfCell hbags hc hy).side i).through :=
  OddPath.closed_eq_through_of_short _ _ hl (c.cellShort_chord hbags hc hy i hl)

end MatchingFPRAS.Transport.IndexedCycle

namespace MatchingFPRAS.Transport.CellDemands

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L} {G : SimpleGraph L}

noncomputable local instance : Fintype (BagEdge bags) := Fintype.ofFinite _

variable {hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b}

variable {hG : G.IsAcyclic}

noncomputable instance : Fintype (Demand hbags hG) := Fintype.ofFinite _

namespace Demand

noncomputable def paths (d : Demand hbags hG) := d.cycle.pathsOfCell hbags d.cell d.last_lt

noncomputable def outside (d : Demand hbags hG) := d.1.1.val \ d.cycle.edgeSet

end Demand

abbrev ErrorDemand (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)
    (hG : G.IsAcyclic) :=
  {e : Bool × Demand hbags hG // ∀ i : Fin 4, CellPaths.sideBit i = e.1 →
    (e.2.paths.side i).length ≠ 1}

noncomputable instance : Fintype (ErrorDemand hbags hG) := Fintype.ofFinite _

namespace ErrorDemand

variable (e : ErrorDemand hbags hG)

def bit : Bool := e.val.1

def demand : Demand hbags hG := e.val.2

def X : Fin 4 := if e.bit then 2 else 3

def Y : Fin 4 := if e.bit then 0 else 1

omit [Fintype L] in
lemma X_bit : CellPaths.sideBit e.X = e.bit := by cases hb : e.bit <;> simp [X,hb,CellPaths.sideBit]

omit [Fintype L] in
lemma Y_bit : CellPaths.sideBit e.Y = e.bit := by cases hb : e.bit <;> simp [Y,hb,CellPaths.sideBit]

omit [Fintype L] in
lemma X_ne_Y : e.X ≠ e.Y := by cases hb : e.bit <;> simp [X,Y,hb]

def flags : Fin 64 := if e.bit then 2 else 1

noncomputable def raw := e.demand.raw e.flags

omit [Fintype L] in
lemma raw_injective : Function.Injective (raw (hbags := hbags) (hG := hG)) := by
  intro e f h
  have hf : e.flags = f.flags := congrArg RawDemand.flags h
  have hb : e.bit = f.bit := by
    cases he : e.bit <;> cases hh : f.bit <;> simp_all [flags]
  have hd : e.demand = f.demand := by
    apply Demand.raw_injective e.flags
    simpa only [raw,hf] using h
  apply Subtype.ext
  exact Prod.ext hb hd

end ErrorDemand

variable (height : L → ℝ) (hheight : ∀ l, 0 < height l)

variable (hstep : ∀ a b, G.Adj a b → height a ≤ 2 * height b)

variable (D : ℝ) (hD : 1 ≤ D) (w : BagEdge bags → ℝ)

variable (hw : ∀ e, height e.color / D ≤ w e ∧ w e ≤ 3 * height e.color)

variable (lo hi : ℝ) (hlo : 0 < lo) (hlohi : lo ≤ hi)

namespace Demand

variable (d : Demand hbags hG)

include hheight hstep hD hw hlo hlohi in
lemma exists_switch : ∃ enc : DemandEncoding BagEdge.Incident (d.raw 0),
    enc.first.val = d.outside ∪ d.paths.switched true ∧
    gibbs (fun e => max lo (min hi (w e))) d.1.1 * gibbs (fun e => max lo (min hi (w e))) d.1.2 ≤
      (1000*D)^4 * gibbs (fun e => max lo (min hi (w e))) enc.first *
        gibbs (fun e => max lo (min hi (w e))) enc.second := by
  obtain ⟨enc,he,hw⟩ := d.cycle.actual_switch_encoding hbags height hheight hstep
    d.1.1 d.1.2 d.2.1.cycle_union d.cell d.last_lt 0 true D hD w hw lo hi hlo hlohi
  refine ⟨enc,?_,hw⟩
  exact he.trans (congrArg (fun R => R ∪ d.paths.switched true)
    (d.corners.embeddedPair_outside d.1.1 d.1.2 d.2.1.cycle_union d.paths.chord d.paths.chord_incidence 0))

noncomputable def switchChoice : DemandEncoding BagEdge.Incident (d.raw 0) :=
  (d.exists_switch height hheight hstep D hD w hw lo hi hlo hlohi).choose

lemma switchChoice_spec :
    (d.switchChoice height hheight hstep D hD w hw lo hi hlo hlohi).first.val =
      d.outside ∪ d.paths.switched true ∧
    gibbs (fun e => max lo (min hi (w e))) d.1.1 * gibbs (fun e => max lo (min hi (w e))) d.1.2 ≤
      (1000*D)^4 * gibbs (fun e => max lo (min hi (w e)))
        (d.switchChoice height hheight hstep D hD w hw lo hi hlo hlohi).first *
        gibbs (fun e => max lo (min hi (w e)))
        (d.switchChoice height hheight hstep D hD w hw lo hi hlo hlohi).second :=
  (d.exists_switch height hheight hstep D hD w hw lo hi hlo hlohi).choose_spec

lemma switchChoice_injective : Function.Injective (fun d : Demand hbags hG =>
    (d.switchChoice height hheight hstep D hD w hw lo hi hlo hlohi).finiteCode) := by
  intro d e h
  exact Demand.raw_injective 0 (DemandEncoding.finiteCode_recovers _ _ h)

end Demand

namespace ErrorDemand

variable (e : ErrorDemand hbags hG)

include hheight hstep hD hw hlo hlohi in
lemma exists_errors : ∃ enc₀ enc₁ : DemandEncoding BagEdge.Incident e.raw,
    enc₀.first.val = e.demand.outside ∪ e.demand.paths.orientation e.bit ∧
    enc₁.first.val = e.demand.outside ∪ e.demand.paths.contextOne e.bit e.Y ∧
    (e.demand.paths.side e.X).closed (e.demand.paths.chord e.X) ⊆ enc₀.second.val ∧
    (e.demand.paths.side e.X).closed (e.demand.paths.chord e.X) ⊆ enc₁.second.val ∧
    gibbs (fun e => max lo (min hi (w e))) e.demand.1.1 *
      gibbs (fun e => max lo (min hi (w e))) e.demand.1.2 ≤
      (1000*D)^4 * gibbs (fun e => max lo (min hi (w e))) enc₀.first *
        gibbs (fun e => max lo (min hi (w e))) enc₀.second ∧
    gibbs (fun e => max lo (min hi (w e))) e.demand.1.1 *
      gibbs (fun e => max lo (min hi (w e))) e.demand.1.2 ≤
      (1000*D)^4 * gibbs (fun e => max lo (min hi (w e))) enc₁.first *
        gibbs (fun e => max lo (min hi (w e))) enc₁.second := by
  obtain ⟨enc₀,enc₁,h₀,h₁,hr⟩ := e.demand.cycle.actual_error_encodings hbags height hheight hstep
    e.demand.1.1 e.demand.1.2 e.demand.2.1.cycle_union e.demand.cell e.demand.last_lt
    e.flags e.bit e.X e.Y e.X_bit e.Y_bit e.X_ne_Y e.property D hD w hw lo hi hlo hlohi
  refine ⟨enc₀,enc₁,?_,?_,hr⟩
  · exact h₀.trans (congrArg (fun R => R ∪ e.demand.paths.orientation e.bit)
      (e.demand.corners.embeddedPair_outside e.demand.1.1 e.demand.1.2 e.demand.2.1.cycle_union
        e.demand.paths.chord e.demand.paths.chord_incidence e.flags))
  · exact h₁.trans (congrArg (fun R => R ∪ e.demand.paths.contextOne e.bit e.Y)
      (e.demand.corners.embeddedPair_outside e.demand.1.1 e.demand.1.2 e.demand.2.1.cycle_union
        e.demand.paths.chord e.demand.paths.chord_incidence e.flags))

noncomputable def errorZero : DemandEncoding BagEdge.Incident e.raw :=
  (e.exists_errors height hheight hstep D hD w hw lo hi hlo hlohi).choose

noncomputable def errorOne : DemandEncoding BagEdge.Incident e.raw :=
  (e.exists_errors height hheight hstep D hD w hw lo hi hlo hlohi).choose_spec.choose

lemma errorZero_injective : Function.Injective (fun e : ErrorDemand hbags hG =>
    (e.errorZero height hheight hstep D hD w hw lo hi hlo hlohi).finiteCode) := by
  intro e f h
  exact raw_injective (DemandEncoding.finiteCode_recovers _ _ h)

lemma errorOne_injective : Function.Injective (fun e : ErrorDemand hbags hG =>
    (e.errorOne height hheight hstep D hD w hw lo hi hlo hlohi).finiteCode) := by
  intro e f h
  exact raw_injective (DemandEncoding.finiteCode_recovers _ _ h)

end ErrorDemand

end MatchingFPRAS.Transport.CellDemands

namespace MatchingFPRAS.Transport.OddPath

variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]

variable {inc : E → V → Prop} (p : OddPath inc) (chord : E)

variable (hlong : 3 ≤ p.length)

variable (hc : ∀ v, inc chord v ↔ v = p.vertex 0 ∨ v = p.vertex p.length)

def closedCycle : IndexedCycle inc where
  size := p.length + 1
  four_le := by omega
  even := by have := p.odd; omega
  vertex i := p.vertex i
  simple := by
    intro i j h
    exact Fin.ext (p.simple ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ h)
  edge i := if i.val < p.length then p.edge i else chord
  incidence := by
    intro i v
    by_cases hi : i.val < p.length
    · rw [ite_eq_left hi,p.incidence i hi]
      have hm : (i.val + 1) % (p.length + 1) = i.val + 1 := Nat.mod_eq_of_lt (by omega)
      simp only [hm]
    · have hil : i.val = p.length := by omega
      rw [ite_eq_right hi,hc]
      simp only [hil,Nat.mod_self]
      exact or_comm

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
lemma closedCycle_edgeAt (i : ℕ) (hi : i < p.length) :
    (p.closedCycle chord hlong hc).edgeAt i = p.edge i := by
  simp only [IndexedCycle.edgeAt,IndexedCycle.index,closedCycle]
  rw [Nat.mod_eq_of_lt (by omega),ite_eq_left hi]

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
lemma closedCycle_chord :
    (p.closedCycle chord hlong hc).edgeAt p.length = chord := by
  simp [IndexedCycle.edgeAt,IndexedCycle.index,closedCycle,Nat.mod_eq_of_lt (by omega : p.length < p.length+1)]

omit [Fintype V] [DecidableEq V] in
lemma closedCycle_parity_zero :
    (p.closedCycle chord hlong hc).parityPattern 0 = p.through := by
  ext e
  simp only [IndexedCycle.parityPattern,IndexedCycle.mem_intervalPattern,through,
    pathPattern,Finset.mem_image,Finset.mem_filter,Finset.mem_Ico]
  constructor
  · rintro ⟨i,hi,hj,hp,he⟩
    have hil : i < p.length := by
      change i < p.length + 1 at hj
      have := p.odd
      omega
    exact ⟨i,⟨⟨by omega,hil⟩,by simpa using hp⟩,
      (p.closedCycle_edgeAt chord hlong hc i hil).symm.trans he⟩
  · rintro ⟨i,⟨hi,hp⟩,he⟩
    refine ⟨i,by omega,by change i < p.length+1; omega,?_,?_⟩
    · simpa using hp
    · exact (p.closedCycle_edgeAt chord hlong hc i hi.2).trans he

omit [Fintype V] [DecidableEq V] in
lemma closedCycle_parity_one :
    (p.closedCycle chord hlong hc).parityPattern 1 = p.closed chord := by
  ext e
  simp only [IndexedCycle.parityPattern,IndexedCycle.mem_intervalPattern,closed,
    interior,pathPattern,Finset.mem_union,Finset.mem_image,Finset.mem_filter,
    Finset.mem_Ico,Finset.mem_singleton]
  constructor
  · rintro ⟨i,hi,hj,hp,he⟩
    change i < p.length+1 at hj
    by_cases hil : i < p.length
    · left
      refine ⟨i,⟨⟨by omega,?_⟩,?_⟩, (p.closedCycle_edgeAt chord hlong hc i hil).symm.trans he⟩
      · have := p.odd; omega
      · omega
    · right
      have hie : i = p.length := by omega
      subst i
      exact he.symm.trans (p.closedCycle_chord chord hlong hc)
  · rintro (⟨i,⟨hi,hp⟩,he⟩ | he)
    · refine ⟨i,by omega,by change i < p.length+1; omega,by omega,?_⟩
      exact (p.closedCycle_edgeAt chord hlong hc i (by omega)).trans he
    · exact ⟨p.length,by omega,by change p.length < p.length+1; omega,
        p.odd,(p.closedCycle_chord chord hlong hc).trans he.symm⟩

end MatchingFPRAS.Transport.OddPath

namespace MatchingFPRAS.Transport

variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]

variable {inc : E → V → Prop}

namespace IndexedCycle

variable (c : IndexedCycle inc)

omit [Fintype V] [DecidableEq V] in
lemma edgeSet_eq_parity_union : c.edgeSet = c.parityPattern 0 ∪ c.parityPattern 1 := by
  ext e
  simp only [mem_edgeSet,parityPattern,mem_intervalPattern,Finset.mem_union]
  constructor
  · rintro ⟨i,hi,he⟩
    have hp : i % 2 = 0 ∨ i % 2 = 1 := by omega
    rcases hp with hp | hp
    · exact Or.inl ⟨i,by omega,hi,hp,he⟩
    · exact Or.inr ⟨i,by omega,hi,hp,he⟩
  · rintro (⟨i,_,hi,_,he⟩ | ⟨i,_,hi,_,he⟩) <;> exact ⟨i,hi,he⟩

omit [Fintype V] [DecidableEq V] in
lemma zero_mem_parity : c.edgeAt 0 ∈ c.parityPattern 0 := by
  apply (c.mem_intervalPattern _ _ _ _).mpr
  exact ⟨0,le_rfl,by have := c.four_le; omega,rfl,rfl⟩

end IndexedCycle

abbrev PatternCode (inc : E → V → Prop) :=
  {s : Finset E × Finset E // ∃ c : IndexedCycle inc,
    c.parityPattern 0 = s.1 ∧ c.parityPattern 1 = s.2}

end MatchingFPRAS.Transport

end OAI
