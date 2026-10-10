import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.Components
import OAI.Combinatorics.MatchingCount.Sampling.Sewn

namespace OAI

namespace MatchingFPRAS.Transport.IndexedCycle

variable {V L : Type*} [Fintype V] [DecidableEq V] [DecidableEq L] [Fintype L]

variable {bags : V → Finset L} (c : IndexedCycle (BagEdge.Incident (bags := bags)))

variable {G : SimpleGraph L}

variable (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)

noncomputable def chosenChord (x y : ℕ) : BagEdge bags := by
  classical
  exact if h : x < y ∧ y < c.size ∧ (c.labelCycle hbags).Admissible x y then
    c.chord hbags x y h.1 h.2.1 h.2.2 else c.edgeAt 0

omit [Fintype V] [DecidableEq V] [Fintype L] in
lemma chosenChord_eq (x y : ℕ) (hxy : x < y) (hy : y < c.size)
    (ha : (c.labelCycle hbags).Admissible x y) :
    c.chosenChord hbags x y = c.chord hbags x y hxy hy ha := by
  unfold chosenChord
  rw [dite_eq_left (show x < y ∧ y < c.size ∧ (c.labelCycle hbags).Admissible x y from ⟨hxy,hy,ha⟩)]

noncomputable def diagramGain (R : Finset (BagEdge bags)) (f : Finset (BagEdge bags) → ℝ)
    (x y : ℕ) : ℝ := c.signedGain R f x y (c.chosenChord hbags x y)

noncomputable def diagramTerm (R : Finset (BagEdge bags)) (f : Finset (BagEdge bags) → ℝ)
    (x p q y : ℕ) : ℝ := by
  classical
  exact if h : (c.labelCycle hbags).Cell x p q y ∧ y < c.size then
    (c.cellCorners hbags h.1 h.2).signedLocalTerm (c.cellChords hbags h.1 h.2)
      (c.cellChords_incidence hbags h.1 h.2) R f else 0

omit [Fintype V] [Fintype L] in
lemma diagramGain_short (R : Finset (BagEdge bags)) (f : Finset (BagEdge bags) → ℝ)
    (x : ℕ) (hx : x + 1 < c.size) : c.diagramGain hbags R f x (x+1)=0 := by
  have ha : (c.labelCycle hbags).Admissible x (x+1) := by
    refine ⟨(c.edgeAt x).color, (c.edge_color_fixed hbags x).1, ?_⟩
    simpa only [Nat.cast_add, Nat.cast_one] using (c.edge_color_fixed hbags x).2
  unfold diagramGain
  rw [c.chosenChord_eq hbags x (x+1) (by omega) hx ha,
    c.chord_short hbags _ _ _ _ _ rfl]
  exact c.signedGain_short R f x hx

omit [Fintype V] [Fintype L] in
lemma diagramGain_root (R : Finset (BagEdge bags)) (f : Finset (BagEdge bags) → ℝ) :
    c.diagramGain hbags R f 0 (c.size-1) =
      f (R ∪ c.parityPattern 0) - f (R ∪ c.parityPattern 1) := by
  have hm := c.four_le
  have ha : (c.labelCycle hbags).Admissible 0 (c.size-1) := by
    refine ⟨(c.edgeAt (c.size-1)).color, ?_, (c.edge_color_fixed hbags (c.size-1)).1⟩
    have hh := (c.edge_color_fixed hbags (c.size-1)).2
    have he : ((c.size-1 : ℕ) : ℤ)+1 = (0 : ℤ)+c.size := by omega
    rw [he, c.labelSets_periodic hbags] at hh
    simpa only [Nat.cast_zero] using hh
  unfold diagramGain
  rw [c.chosenChord_eq hbags 0 (c.size-1) (by omega) (by omega) ha,
    c.chord_wrap hbags _ _ _ _ _ ⟨rfl,by omega⟩]
  exact c.signedGain_root R f

omit [Fintype V] [Fintype L] in
lemma diagram_cell_recurrence (R : Finset (BagEdge bags)) (f : Finset (BagEdge bags) → ℝ)
    (x p q y : ℕ) (hc : (c.labelCycle hbags).Cell x p q y) (hy : y < c.size) :
    c.diagramGain hbags R f x y = c.diagramTerm hbags R f x p q y +
      c.diagramGain hbags R f x p + c.diagramGain hbags R f p q +
      c.diagramGain hbags R f q y := by
  have hxp := hc.first_pos
  have hpq := hc.middle_pos
  have hqy := hc.third_pos
  have he : (c.labelCycle hbags).Admissible x y := by
    obtain ⟨l,hl₁,hl₂⟩ := hc.exterior
    exact ⟨l,hl₂,hl₁⟩
  unfold diagramGain diagramTerm
  rw [dite_eq_left ⟨hc,hy⟩,
    c.chosenChord_eq hbags x y (by omega) hy he,
    c.chosenChord_eq hbags x p hxp (by omega) hc.first,
    c.chosenChord_eq hbags p q hpq (by omega) hc.middle,
    c.chosenChord_eq hbags q y hqy hy hc.third]
  exact (c.cellCorners hbags hc hy).signed_cell_recurrence
    (c.cellChords hbags hc hy) (c.cellChords_incidence hbags hc hy) R f
    BagEdge.exists_incident

omit [Fintype V] [Fintype L] in
theorem sum_cells_identity (R : Finset (BagEdge bags)) (f : Finset (BagEdge bags) → ℝ)
    (Q : MatchingFPRAS.Cells.CycleData.Subdivision (c.labelCycle hbags) 0 (c.size-1)) :
    f (R ∪ c.parityPattern 0) - f (R ∪ c.parityPattern 1) =
      Q.sumCells (c.diagramTerm hbags R f) := by
  rw [← c.diagramGain_root hbags R f]
  exact Q.signed_cancellation_bounded (c.diagramGain hbags R f) (c.diagramTerm hbags R f)
    (c.diagramGain_short hbags R f) (c.diagram_cell_recurrence hbags R f)
    (by have := c.four_le; omega)

end MatchingFPRAS.Transport.IndexedCycle

namespace MatchingFPRAS.Cells.CycleData

variable {L : Type*} [DecidableEq L] {G : SimpleGraph L} {m : ℕ} {C : CycleData G m}

@[ext] structure CellIndex where
  x : ℕ
  p : ℕ
  q : ℕ
  y : ℕ
  deriving DecidableEq

namespace Subdivision

variable {x y : ℕ}

def cellList : {x y : ℕ} → Subdivision C x y → List CellIndex
  | _, _, .edge _ => []
  | x, y, .node (p := p) (q := q) _ Q₁ Q₂ Q₃ =>
      ⟨x,p,q,y⟩ :: (Q₁.cellList ++ Q₂.cellList ++ Q₃.cellList)

lemma mem_cellList {Q : Subdivision C x y} {a : CellIndex} (ha : a ∈ Q.cellList) :
    x ≤ a.x ∧ a.y ≤ y ∧ C.Cell a.x a.p a.q a.y := by
  induction Q with
  | edge h => simp [cellList] at ha
  | @node x p q y h Q₁ Q₂ Q₃ ih₁ ih₂ ih₃ =>
    simp only [cellList, List.mem_cons, List.mem_append] at ha
    rcases ha with rfl | (ha | ha) | ha
    · exact ⟨le_rfl, le_rfl, h⟩
    · obtain ⟨hx,hy,hc⟩ := ih₁ ha
      exact ⟨hx, by have := h.middle_pos; have := h.third_pos; omega, hc⟩
    · obtain ⟨hx,hy,hc⟩ := ih₂ ha
      exact ⟨by have := h.first_pos; omega, by have := h.third_pos; omega, hc⟩
    · obtain ⟨hx,hy,hc⟩ := ih₃ ha
      exact ⟨by have := h.first_pos; have := h.middle_pos; omega, hy, hc⟩

lemma cellList_length (Q : Subdivision C x y) : Q.cellList.length = Q.cells := by
  induction Q with
  | edge h => rfl
  | node h _ _ _ ih₁ ih₂ ih₃ => simp only [cellList, List.length_cons,
      List.length_append, cells, ih₁, ih₂, ih₃]; omega

lemma cellList_separated {x₁ y₁ x₂ y₂ : ℕ} (Q₁ : Subdivision C x₁ y₁)
    (Q₂ : Subdivision C x₂ y₂) (h : y₁ ≤ x₂) :
    ∀ a ∈ Q₁.cellList, ∀ b ∈ Q₂.cellList, a ≠ b := by
  intro a ha b hb hab
  subst b
  obtain ⟨_,hy,hc⟩ := mem_cellList ha
  obtain ⟨hx,_,_⟩ := mem_cellList hb
  have := hc.first_pos
  have := hc.middle_pos
  have := hc.third_pos
  omega

lemma cellList_nodup (Q : Subdivision C x y) : Q.cellList.Nodup := by
  induction Q with
  | edge h => simp [cellList]
  | @node x p q y h Q₁ Q₂ Q₃ ih₁ ih₂ ih₃ =>
    rw [cellList, List.nodup_cons]
    refine ⟨?_, List.nodup_append.mpr ⟨List.nodup_append.mpr ⟨ih₁, ih₂,
      cellList_separated Q₁ Q₂ le_rfl⟩, ih₃, ?_⟩⟩
    · intro ha
      simp only [List.mem_append] at ha
      rcases ha with (ha | ha) | ha
      · have hh := (mem_cellList ha).2.1
        have := h.middle_pos
        have := h.third_pos
        simp only at hh
        omega
      · have hh := (mem_cellList ha).1
        have := h.first_pos
        simp only at hh
        omega
      · have hh := (mem_cellList ha).1
        have := h.first_pos
        have := h.middle_pos
        simp only at hh
        omega
    · intro a ha b hb
      rcases List.mem_append.mp ha with ha | ha
      · exact cellList_separated Q₁ Q₃ (le_of_lt h.middle_pos) a ha b hb
      · exact cellList_separated Q₂ Q₃ le_rfl a ha b hb

def cellSet (Q : Subdivision C x y) : Finset CellIndex := Q.cellList.toFinset

lemma cellSet_card (Q : Subdivision C x y) : Q.cellSet.card = Q.cells := by
  rw [cellSet, List.toFinset_card_of_nodup Q.cellList_nodup, Q.cellList_length]

lemma sumCells_eq_sum (Q : Subdivision C x y) (f : ℕ → ℕ → ℕ → ℕ → ℝ) :
    Q.sumCells f = ∑ a ∈ Q.cellSet, f a.x a.p a.q a.y := by
  rw [cellSet, List.sum_toFinset _ Q.cellList_nodup]
  induction Q with
  | edge h => rfl
  | node h _ _ _ ih₁ ih₂ ih₃ =>
    simp only [sumCells, cellList, List.map_cons, List.map_append, List.sum_cons,
      List.sum_append, ih₁, ih₂, ih₃]
    ring

end Subdivision

end MatchingFPRAS.Cells.CycleData

namespace MatchingFPRAS.Transport.IndexedCycle

section

variable {V L : Type*} [Fintype V] [DecidableEq V] [DecidableEq L] [Fintype L]

variable {bags : V → Finset L} (c : IndexedCycle (BagEdge.Incident (bags := bags)))

variable {G : SimpleGraph L}

variable (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)

noncomputable def diagramEnergy (R : Finset (BagEdge bags)) (f : Finset (BagEdge bags) → ℝ)
    (x p q y : ℕ) : ℝ := by
  classical
  exact if h : (c.labelCycle hbags).Cell x p q y ∧ y < c.size then
    let P := c.pathsOfCell hbags h.1 h.2
    (f (R ∪ P.switched true) - f (R ∪ P.switched false))^2 +
      (P.contextError R f true 2 0)^2 + (P.contextError R f false 3 1)^2
    else 0

omit [Fintype V] [Fintype L] in
lemma diagramEnergy_nonneg (R : Finset (BagEdge bags))
    (f : Finset (BagEdge bags) → ℝ) (x p q y : ℕ) :
    0 ≤ c.diagramEnergy hbags R f x p q y := by
  unfold diagramEnergy
  split_ifs <;> positivity

omit [Fintype V] [Fintype L] in
lemma diagramTerm_sq_le (R : Finset (BagEdge bags))
    (f : Finset (BagEdge bags) → ℝ) (x p q y : ℕ) :
    (c.diagramTerm hbags R f x p q y)^2 ≤ 3 * c.diagramEnergy hbags R f x p q y := by
  classical
  by_cases h : (c.labelCycle hbags).Cell x p q y ∧ y < c.size
  · simp only [diagramTerm, diagramEnergy, dite_eq_left h]
    let P := c.pathsOfCell hbags h.1 h.2
    let a := f (R ∪ P.switched true) - f (R ∪ P.switched false)
    let b := P.contextError R f true 2 0
    let d := P.contextError R f false 3 1
    change (if x%2=0 then a+b-d else -(a+b-d))^2 ≤ 3*(a^2+b^2+d^2)
    split_ifs <;> nlinarith [sq_nonneg (a-b), sq_nonneg (a+d), sq_nonneg (b+d)]
  · simp only [diagramTerm, diagramEnergy, dite_eq_right h, zero_pow (by decide : 2≠0), mul_zero,
      le_refl]

omit [Fintype L] in
theorem cycle_cell_square_bound (R : Finset (BagEdge bags))
    (f : Finset (BagEdge bags) → ℝ)
    (Q : MatchingFPRAS.Cells.CycleData.Subdivision (c.labelCycle hbags) 0 (c.size-1)) :
    (f (R ∪ c.parityPattern 0) - f (R ∪ c.parityPattern 1))^2 ≤
      3 * (Fintype.card V : ℝ) *
        ∑ a ∈ Q.cellSet, c.diagramEnergy hbags R f a.x a.p a.q a.y := by
  classical
  let t := fun a : MatchingFPRAS.Cells.CycleData.CellIndex =>
    c.diagramTerm hbags R f a.x a.p a.q a.y
  let e := fun a : MatchingFPRAS.Cells.CycleData.CellIndex =>
    c.diagramEnergy hbags R f a.x a.p a.q a.y
  have hsum : 0 ≤ ∑ a ∈ Q.cellSet, e a :=
    Finset.sum_nonneg (fun a _ => c.diagramEnergy_nonneg hbags R f a.x a.p a.q a.y)
  have hsize : c.size ≤ Fintype.card V := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective c.vertex c.simple
  have hcells : (Q.cellSet.card : ℝ) ≤ (Fintype.card V : ℝ) := by
    apply Nat.cast_le.mpr
    rw [Q.cellSet_card]
    have := Q.cells_length
    omega
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Q.cellSet t (fun _ => (1:ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  have he : ∑ a ∈ Q.cellSet, (t a)^2 ≤ 3 * ∑ a ∈ Q.cellSet, e a := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun a _ => c.diagramTerm_sq_le hbags R f a.x a.p a.q a.y)
  rw [c.sum_cells_identity hbags R f Q, Q.sumCells_eq_sum]
  change (∑ a ∈ Q.cellSet, t a)^2 ≤ 3 * (Fintype.card V : ℝ) * ∑ a ∈ Q.cellSet, e a
  calc
    _ ≤ (∑ a ∈ Q.cellSet, t a^2) * (Q.cellSet.card : ℝ) := hcs
    _ ≤ (3 * ∑ a ∈ Q.cellSet, e a) * (Q.cellSet.card : ℝ) :=
      mul_le_mul_of_nonneg_right he (Nat.cast_nonneg _)
    _ ≤ (3 * ∑ a ∈ Q.cellSet, e a) * (Fintype.card V : ℝ) :=
      mul_le_mul_of_nonneg_left hcells (mul_nonneg (by norm_num) hsum)
    _ = _ := by ring

end

variable {V L : Type*} [Fintype V] [DecidableEq V] [DecidableEq L] [Fintype L]

variable {bags : V → Finset L} (c : IndexedCycle (BagEdge.Incident (bags := bags)))

variable {G : SimpleGraph L}

variable (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)

noncomputable def subdivision (hG : G.IsAcyclic) :
    MatchingFPRAS.Cells.CycleData.Subdivision (c.labelCycle hbags) 0 (c.size-1) :=
  Classical.choice ((c.labelCycle hbags).quadrangulate hG c.four_le c.even)

omit [Fintype L] in
theorem exchange_cell_square_bound {M N : Finset (BagEdge bags)}
    (hM : MatchingOn BagEdge.Incident M Finset.univ)
    (hN : MatchingOn BagEdge.Incident N Finset.univ)
    (hU : ∀ i, c.edgeAt i ∈ M ∪ N) (hG : G.IsAcyclic)
    (f : Finset (BagEdge bags) → ℝ) :
    (f M - f (exchange M N c.edgeSet))^2 ≤
      3 * (Fintype.card V : ℝ) *
        ∑ a ∈ (c.subdivision hbags hG).cellSet,
          c.diagramEnergy hbags (M \ c.edgeSet) f a.x a.p a.q a.y := by
  classical
  have hU' : ∀ i, c.edgeAt i ∈ N ∪ M := by simpa only [Finset.union_comm] using hU
  have hpat := c.inter_edgeSet_parity hM hN hU
  have hpat' := c.inter_edgeSet_parity hN hM hU'
  have hcomp := c.cycle_edge_mem_complement hM hN hU 0
  have hMsplit : M = (M \ c.edgeSet) ∪ M ∩ c.edgeSet := by
    ext e
    simp only [Finset.mem_union,Finset.mem_sdiff,Finset.mem_inter]
    tauto
  have hX : exchange M N c.edgeSet = (M \ c.edgeSet) ∪ N ∩ c.edgeSet := rfl
  rw [hpat] at hMsplit
  rw [hpat'] at hX
  have hb := c.cycle_cell_square_bound hbags (M \ c.edgeSet) f (c.subdivision hbags hG)
  by_cases he : c.edgeAt 0 ∈ M
  · have hn : c.edgeAt 0 ∉ N := fun hn => (hcomp.mp hn) he
    simp only [ite_eq_left he,ite_eq_right hn] at hMsplit hX
    calc
      _ = (f ((M \ c.edgeSet) ∪ c.parityPattern 0) -
          f ((M \ c.edgeSet) ∪ c.parityPattern 1))^2 := by rw [← hMsplit,← hX]
      _ ≤ _ := hb
  · have hn : c.edgeAt 0 ∈ N := by tauto
    simp only [ite_eq_right he,ite_eq_left hn] at hMsplit hX
    calc
      _ = (f ((M \ c.edgeSet) ∪ c.parityPattern 1) -
          f ((M \ c.edgeSet) ∪ c.parityPattern 0))^2 := by rw [← hMsplit,← hX]
      _ = (f ((M \ c.edgeSet) ∪ c.parityPattern 0) -
          f ((M \ c.edgeSet) ∪ c.parityPattern 1))^2 := by ring
      _ ≤ _ := hb

end MatchingFPRAS.Transport.IndexedCycle

namespace MatchingFPRAS.Transport

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable {inc : E → V → Prop}

abbrev LongComponent (p : PM inc × PM inc) :=
  {S : Finset E // ∃ c : IndexedCycle inc, c.edgeSet = S ∧ ∀ i, c.edgeAt i ∈ p.1.val ∪ p.2.val}

namespace LongComponent

variable {p : PM inc × PM inc} (S : LongComponent p)

noncomputable instance : Fintype (LongComponent p) := Fintype.ofFinite _

noncomputable def cycle : IndexedCycle inc := S.property.choose

omit [DecidableEq V] [Fintype E] in
lemma cycle_set : S.cycle.edgeSet = S.val := S.property.choose_spec.1

omit [DecidableEq V] [Fintype E] in
lemma cycle_union : ∀ i, S.cycle.edgeAt i ∈ p.1.val ∪ p.2.val := S.property.choose_spec.2

omit [DecidableEq V] [Fintype E] in
lemma mem_components : S.val ∈ components (inc := inc) (p.1.val ∪ p.2.val) :=
  S.cycle_set ▸ S.cycle.edgeSet_mem_components p.1.property p.2.property S.cycle_union

omit [DecidableEq V] [Fintype E] in
lemma anchor_recovers {T : LongComponent p} (h : S.cycle.edgeAt 0 = T.cycle.edgeAt 0) : S = T := by
  apply Subtype.ext
  rw [← S.cycle_set,← T.cycle_set,S.cycle.edgeSet_eq_component p.1.property p.2.property S.cycle_union,
    T.cycle.edgeSet_eq_component p.1.property p.2.property T.cycle_union,h]

end LongComponent

end MatchingFPRAS.Transport

namespace MatchingFPRAS.Transport.CellDemands

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L}

noncomputable local instance : Fintype (BagEdge bags) := Fintype.ofFinite _

variable {G : SimpleGraph L}

variable (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)

variable (hG : G.IsAcyclic)

abbrev Demand := Σ p : PM (BagEdge.Incident (bags := bags)) × PM BagEdge.Incident,
  Σ S : LongComponent p, ↥(S.cycle.subdivision hbags hG).cellSet

end MatchingFPRAS.Transport.CellDemands

end OAI
