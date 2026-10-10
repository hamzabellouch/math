import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.ColoredEdge

namespace OAI

namespace MatchingFPRAS.Transport
variable {V L : Type*} [DecidableEq V]
variable {E : Type*} [DecidableEq E] (inc : E → V → Prop)
namespace OddPath

variable {inc}

variable (p : OddPath inc)

def span : Finset V := (Finset.Icc 0 p.length).image p.vertex

def inside : Finset V := (Finset.Icc 1 (p.length - 1)).image p.vertex

def ends : Finset V := {p.vertex 0, p.vertex p.length}

def through : Finset E := pathPattern p.edge 0 p.length

def interior : Finset E := pathPattern p.edge 1 (p.length - 1)

def closed (chord : E) : Finset E := p.interior ∪ {chord}

def boundary : Finset E := if p.length = 1 then {p.edge 0}
  else {p.edge 0, p.edge (p.length - 1)}

def repaired (repair : E) : Finset E := if p.length = 1 then ∅
  else pathPattern p.edge 2 (p.length - 2) ∪ {repair}

def repairAdded (repair : E) : Multiset E := if p.length = 1 then 0 else {repair}

lemma through_matching : MatchingOn inc p.through p.span := by
  apply pathPattern_matching inc p.vertex p.edge 0 p.length p.positive
  · simpa using p.odd
  · exact p.simple
  · intro i _ hi v
    exact p.incidence i hi v

lemma interior_matching : MatchingOn inc p.interior p.inside := by
  by_cases h : p.length = 1
  · simpa [interior, inside, h, pathPattern] using
      (empty_matching (V := V) (E := E) inc)
  · have hpos := p.positive
    have hodd := p.odd
    apply pathPattern_matching inc p.vertex p.edge 1 (p.length - 1)
    · omega
    · omega
    · intro i hi j hj heq
      simp only [Set.mem_Icc] at hi hj
      exact p.simple ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ heq
    · intro i hi hj v
      exact p.incidence i (by omega) v

omit [DecidableEq E] in
lemma inside_disjoint_ends : Disjoint p.inside p.ends := by
  apply Finset.disjoint_left.mpr
  intro v hv hw
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨hil, hih⟩ := Finset.mem_Icc.mp hi
  simp only [ends, Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with h | h
  · have hh := p.simple ⟨by omega, by omega⟩ ⟨le_rfl, Nat.zero_le _⟩ h
    omega
  · have hh := p.simple ⟨by omega, by omega⟩ ⟨Nat.zero_le _, le_rfl⟩ h
    omega

omit [DecidableEq E] in
lemma inside_union_ends : p.inside ∪ p.ends = p.span := by
  ext v
  simp only [inside, ends, span, Finset.mem_union, Finset.mem_image,
    Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (⟨i, hi, rfl⟩ | rfl | rfl)
    · exact ⟨i, ⟨by omega, by omega⟩, rfl⟩
    · exact ⟨0, ⟨le_rfl, Nat.zero_le _⟩, rfl⟩
    · exact ⟨p.length, ⟨Nat.zero_le _, le_rfl⟩, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    by_cases h0 : i = 0
    · exact Or.inr (Or.inl (congrArg p.vertex h0))
    by_cases hh : i = p.length
    · exact Or.inr (Or.inr (congrArg p.vertex hh))
    · exact Or.inl ⟨i, ⟨by omega, by omega⟩, rfl⟩

lemma closed_matching (chord : E)
    (hc : ∀ v, inc chord v ↔ v = p.vertex 0 ∨ v = p.vertex p.length) :
    MatchingOn inc (p.closed chord) p.span := by
  have hm := p.interior_matching.union (singleton_matching inc chord _ _ hc)
    p.inside_disjoint_ends
  change MatchingOn inc (p.closed chord) (p.inside ∪ p.ends) at hm
  rwa [p.inside_union_ends] at hm

lemma repaired_matching (repair : E)
    (hr : p.length ≠ 1 → ∀ v,
      inc repair v ↔ v = p.vertex 1 ∨ v = p.vertex (p.length - 1)) :
    MatchingOn inc (p.repaired repair) p.inside := by
  by_cases h : p.length = 1
  · simpa [repaired, inside, h] using (empty_matching (V := V) (E := E) inc)
  · have hpos := p.positive
    have hodd := p.odd
    simp only [repaired, ite_eq_right h]
    simpa only [Nat.zero_add, inside] using repairedThrough_matching inc p.vertex p.edge 0
      p.length (by omega) (by simpa using p.odd) p.simple
      (fun i _ hi v => p.incidence i hi v) repair (hr h)

lemma closed_val (chord : E)
    (hc : ∀ v, inc chord v ↔ v = p.vertex 0 ∨ v = p.vertex p.length)
    (hinc : ∀ e, ∃ v, inc e v) :
    (p.closed chord).val = p.interior.val + {chord} := by
  apply union_val_add
  exact p.interior_matching.disjoint_edges (singleton_matching inc chord _ _ hc)
    hinc p.inside_disjoint_ends

omit [DecidableEq V] [DecidableEq E] in
lemma edge_injective : Set.InjOn p.edge (Set.Ico 0 p.length) := by
  intro i hi j hj heq
  simp only [Set.mem_Ico] at hi hj
  have hiinc : inc (p.edge i) (p.vertex i) := (p.incidence i hi.2 _).mpr (Or.inl rfl)
  rw [heq] at hiinc
  have hjinc : inc (p.edge j) (p.vertex (i+1)) := by
    rw [← heq]
    exact (p.incidence i hi.2 _).mpr (Or.inr rfl)
  have hi₁ := (p.incidence j hj.2 _).mp hiinc
  have hi₂ := (p.incidence j hj.2 _).mp hjinc
  have hs₁ : i = j ∨ i = j + 1 := hi₁.imp
    (p.simple ⟨by omega, by omega⟩ ⟨by omega, by omega⟩)
    (p.simple ⟨by omega, by omega⟩ ⟨by omega, by omega⟩)
  have hs₂ : i+1 = j ∨ i+1 = j+1 := hi₂.imp
    (p.simple ⟨by omega, by omega⟩ ⟨by omega, by omega⟩)
    (p.simple ⟨by omega, by omega⟩ ⟨by omega, by omega⟩)
  omega

omit [DecidableEq V] in
lemma boundary_card : p.boundary.card = if p.length = 1 then 1 else 2 := by
  by_cases h : p.length = 1
  · simp [boundary, h]
  · have hpos := p.positive
    have hodd := p.odd
    have hneq : p.edge 0 ≠ p.edge (p.length - 1) := by
      intro heq
      have hh := p.edge_injective ⟨le_rfl, hpos⟩ ⟨by omega, by omega⟩ heq
      omega
    simp [boundary, h, hneq]

omit [DecidableEq V] in
lemma repair_conservation (repair : E)
    (hr : p.length ≠ 1 → ∀ v,
      inc repair v ↔ v = p.vertex 1 ∨ v = p.vertex (p.length - 1))
    (_hinc : ∀ e, ∃ v, inc e v) :
    (p.repaired repair).val + p.boundary.val = p.through.val + p.repairAdded repair := by
  by_cases h : p.length = 1
  · have ht : p.through = {p.edge 0} := by simp [through, pathPattern, h, Finset.filter_singleton]
    simp only [repaired, boundary, repairAdded, ite_eq_left h, ht, Finset.empty_val,
      zero_add, add_zero]
  · have hpos := p.positive
    have hodd := p.odd
    have hlen : 3 ≤ p.length := by omega
    let trim := pathPattern p.edge 2 (p.length - 2)
    have ht : p.through = trim ∪ p.boundary := by
      simpa only [through, trim, Nat.zero_add, boundary, ite_eq_right h] using
        pathPattern_boundary p.edge 0 p.length hlen (by simpa using hodd)
    have hbdis : Disjoint trim p.boundary := by
      apply Finset.disjoint_left.mpr
      intro e he hb
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hi, _⟩ := Finset.mem_filter.mp hi
      obtain ⟨hil, hih⟩ := Finset.mem_Ico.mp hi
      simp only [boundary, ite_eq_right h, Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with hh | hh
      · have hh' := p.edge_injective ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hh
        omega
      · have hh' := p.edge_injective ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hh
        omega
    have hrdis : Disjoint trim {repair} := by
      apply Finset.disjoint_left.mpr
      intro e he hr'
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hi, _⟩ := Finset.mem_filter.mp hi
      obtain ⟨hil, hih⟩ := Finset.mem_Ico.mp hi
      have heq := Finset.mem_singleton.mp hr'
      have hiinc : inc repair (p.vertex i) := by
        rw [← heq]
        exact (p.incidence i (by omega) _).mpr (Or.inl rfl)
      rcases (hr h _).mp hiinc with hh | hh
      · have hh' := p.simple ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hh
        omega
      · have hh' := p.simple ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hh
        omega
    rw [ht, union_val_add hbdis]
    simp only [repaired, ite_eq_right h, repairAdded]
    rw [union_val_add hrdis]
    simp only [Finset.singleton_val]
    ac_rfl

end OddPath

structure CellPaths where
  side : Fin 4 → OddPath inc
  joins : ∀ i, (side i).vertex (side i).length = (side (i+1)).vertex 0
  corners_injective : Function.Injective fun i => (side i).vertex 0
  interiors_disjoint : Pairwise fun i j => Disjoint (side i).inside (side j).inside
  interior_ends_disjoint : ∀ i j, Disjoint (side i).inside (side j).ends
  chord : Fin 4 → E
  chord_incidence : ∀ i v, inc (chord i) v ↔
    v = (side i).vertex 0 ∨ v = (side i).vertex (side i).length

end MatchingFPRAS.Transport

end OAI
