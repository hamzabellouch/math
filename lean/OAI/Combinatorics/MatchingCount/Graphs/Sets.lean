import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.IndexedCycle
import OAI.Combinatorics.MatchingCount.Graphs.ArcData

namespace OAI

namespace MatchingFPRAS.Cells
open SimpleGraph

variable {L : Type*} {G : SimpleGraph L}
namespace CycleData

variable [DecidableEq L] {m : ℕ} (C : CycleData G m)

def sets (i : ℤ) : Finset L := {C.labels (i - 1), C.labels i}

def Admissible (x y : ℕ) : Prop := ∃ l, l ∈ C.sets x ∧ l ∈ C.sets y

def Good (x y : ℕ) : Prop := y = x + 1 ∨ C.Admissible (x + 1) (y - 1)

def ExteriorGood (x y : ℕ) : Prop :=
  y + 1 = x + m ∨ ∃ l, l ∈ C.sets ((y : ℤ) + 1) ∧ l ∈ C.sets ((x : ℤ) - 1)

lemma sets_clique (i : ℤ) : ∀ u ∈ C.sets i, ∀ v ∈ C.sets i, u = v ∨ G.Adj u v := by
  intro u hu v hv
  simp only [sets, Finset.mem_insert, Finset.mem_singleton] at hu hv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact Or.inl rfl
  · exact C.adjacent i
  · exact (C.adjacent i).imp Eq.symm (fun h => h.symm)
  · exact Or.inl rfl

def arc (x s : ℕ) : ArcData G s where
  labels i := C.labels ((x : ℤ) + i)
  sets i := C.sets ((x : ℤ) + i)
  left_mem i _ := by simp [sets]
  right_mem i _ := by
    simp only [sets, Finset.mem_insert, Finset.mem_singleton]
    left
    congr 1
    push_cast
    omega
  clique i _ := C.sets_clique ((x : ℤ) + i)

lemma arc_admissible (x s u v : ℕ) :
    (C.arc x s).Admissible u v ↔ C.Admissible (x + u) (x + v) := by
  simp only [ArcData.Admissible, Admissible, arc, Nat.cast_add]

lemma arc_good (x s u v : ℕ) (huv : u < v) :
    (C.arc x s).Good u v ↔ C.Good (x + u) (x + v) := by
  have hv : 1 ≤ v := by omega
  have h₁ : x + u + 1 = x + (u + 1) := by omega
  have h₂ : x + v - 1 = x + (v - 1) := by omega
  simp only [ArcData.Good, Good, h₁, h₂, ← C.arc_admissible x s]
  constructor
  · rintro (h | h)
    · exact Or.inl (by omega)
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl (by omega)
    · exact Or.inr h

lemma bad_exterior_boundary (x s : ℕ) (hs : 0 < s) (P : L)
    (hP₀ : P ∈ (C.arc x s).sets 0) (hPₛ : P ∈ (C.arc x s).sets s)
    (hbad : ¬ C.ExteriorGood x (x + s)) :
    (C.arc x s).labels 0 = P ∨ (C.arc x s).labels (s - 1) = P := by
  by_contra h
  push Not at h
  rcases h with ⟨hleft, hright⟩
  have hcast : (↑(s - 1) : ℤ) = (s : ℤ) - 1 := by omega
  simp only [arc, Nat.cast_zero, add_zero] at hleft hP₀
  simp only [arc, hcast] at hright
  have h₀ : P = C.labels ((x : ℤ) - 1) := by
    simpa only [sets, Finset.mem_insert, Finset.mem_singleton, or_iff_left hleft.symm] using hP₀
  have hₛ : P = C.labels ((x : ℤ) + s) := by
    have hne : P ≠ C.labels ((x : ℤ) + s - 1) := by
      intro hh
      apply hright
      convert hh.symm using 1
      congr 1
      omega
    simpa only [arc, sets, Finset.mem_insert, Finset.mem_singleton, or_iff_right hne] using hPₛ
  apply hbad
  right
  refine ⟨P, ?_, ?_⟩
  · simp only [sets, Finset.mem_insert, Finset.mem_singleton]
    left
    convert hₛ using 1
    congr 1
    push_cast
    omega
  · simp only [sets, Finset.mem_insert, Finset.mem_singleton]
    exact Or.inr h₀

structure Cell (x p q y : ℕ) : Prop where
  first_pos : x < p
  middle_pos : p < q
  third_pos : q < y
  odd_first : (p - x) % 2 = 1
  odd_middle : (q - p) % 2 = 1
  odd_third : (y - q) % 2 = 1
  odd_exterior : (m - (y - x)) % 2 = 1
  first : C.Admissible x p
  middle : C.Admissible p q
  third : C.Admissible q y
  exterior : C.Admissible y x
  some_good : (C.Good x p ∧ C.Good q y) ∨ (C.Good p q ∧ C.ExteriorGood x y)
  outer_long : 1 < p - x → 1 < y - q → C.Good p q ∧ C.ExteriorGood x y
  middle_exterior_long : 1 < q - p → 1 < m - (y - x) → C.Good x p ∧ C.Good q y

inductive Subdivision (C : CycleData G m) : ℕ → ℕ → Type _ where
  | edge {x y} (short : y = x + 1) : Subdivision C x y
  | node {x p q y} (cell : C.Cell x p q y)
      (first : Subdivision C x p) (middle : Subdivision C p q)
      (third : Subdivision C q y) : Subdivision C x y

lemma cell_of_split (x s : ℕ) (hm : m % 2 = 0) (hs : s % 2 = 1)
    (hbound : x + s < m) (hadm : C.Admissible x (x + s))
    (T : (C.arc x s).Split (C.ExteriorGood x (x + s))) :
    C.Cell x (x + T.p₁) (x + T.p₂) (x + s) := by
  have h₁ := T.positive
  have h₂ := T.ordered
  have h₃ := T.inside
  have ho := T.odd₁
  have he := T.even₂
  have ha₁ : C.Admissible x (x + T.p₁) := by
    simpa only [Nat.add_zero] using (C.arc_admissible x s 0 T.p₁).mp T.first
  have ha₂ := (C.arc_admissible x s T.p₁ T.p₂).mp T.middle
  have ha₃ := (C.arc_admissible x s T.p₂ s).mp T.third
  have hae : C.Admissible (x + s) x := by
    obtain ⟨l, hl₁, hl₂⟩ := hadm
    exact ⟨l, hl₂, hl₁⟩
  have g₁ : (C.arc x s).Good 0 T.p₁ → C.Good x (x + T.p₁) := by
    intro h
    simpa only [Nat.add_zero] using (C.arc_good x s 0 T.p₁ h₁).mp h
  have g₂ := (C.arc_good x s T.p₁ T.p₂ h₂).mp
  have g₃ := (C.arc_good x s T.p₂ s h₃).mp
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      ha₁, ha₂, ha₃, hae, ?_, ?_, ?_⟩
  · rcases T.some_good with ⟨hf, ht⟩ | ⟨hm, hg⟩
    · exact Or.inl ⟨g₁ hf, g₃ ht⟩
    · exact Or.inr ⟨g₂ hm, hg⟩
  · intro hf ht
    obtain ⟨hm, hg⟩ := T.outer_long (by omega) (by omega)
    exact ⟨g₂ hm, hg⟩
  · intro hmiddle _
    obtain ⟨hf, ht⟩ := T.middle_long (by omega)
    exact ⟨g₁ hf, g₃ ht⟩

theorem quadrangulate_arc (hG : G.IsAcyclic) (heven : m % 2 = 0)
    (s : ℕ) : ∀ x, 0 < s → s % 2 = 1 → x + s < m →
      C.Admissible x (x + s) → Nonempty (Subdivision C x (x + s)) := by
  induction s using Nat.strong_induction_on with
  | h s ih =>
    intro x hs hsodd hbound hadm
    by_cases hshort : s = 1
    · exact ⟨.edge (by omega)⟩
    have hslarge : 3 ≤ s := by omega
    obtain ⟨P, hP₀, hPₛ⟩ := hadm
    have hP₀' : P ∈ (C.arc x s).sets 0 := by simpa only [arc, Nat.cast_zero, add_zero] using hP₀
    have hPₛ' : P ∈ (C.arc x s).sets s := by simpa only [arc, Nat.cast_add] using hPₛ
    obtain ⟨T⟩ := (C.arc x s).split hG (C.ExteriorGood x (x + s)) hslarge hsodd P
      hP₀' hPₛ' (C.bad_exterior_boundary x s hs P hP₀' hPₛ')
    have h₁ := T.positive
    have h₂ := T.ordered
    have h₃ := T.inside
    have ho := T.odd₁
    have he := T.even₂
    have cell := C.cell_of_split x s heven hsodd hbound ⟨P, hP₀, hPₛ⟩ T
    obtain ⟨Q₁⟩ := ih T.p₁ (by omega) x h₁ ho (by omega) cell.first
    have eq₂ : x + T.p₁ + (T.p₂ - T.p₁) = x + T.p₂ := by omega
    have eq₃ : x + T.p₂ + (s - T.p₂) = x + s := by omega
    obtain ⟨Q₂⟩ := ih (T.p₂ - T.p₁) (by omega) (x + T.p₁) (by omega) (by omega)
      (by omega) (by simpa only [eq₂] using cell.middle)
    obtain ⟨Q₃⟩ := ih (s - T.p₂) (by omega) (x + T.p₂) (by omega) (by omega)
      (by omega) (by simpa only [eq₃] using cell.third)
    rw [eq₂] at Q₂
    rw [eq₃] at Q₃
    exact ⟨.node cell Q₁ Q₂ Q₃⟩

theorem quadrangulate (hG : G.IsAcyclic) (hm : 4 ≤ m) (heven : m % 2 = 0) :
    Nonempty (Subdivision C 0 (m - 1)) := by
  have hclose : C.labels ((m : ℤ) - 1) = C.labels (-1) := by
    calc
      C.labels ((m : ℤ) - 1) = C.labels (-1 + (m : ℤ)) := congrArg C.labels (by omega)
      _ = C.labels (-1) := C.periodic (-1)
  have hadm : C.Admissible 0 (0 + (m - 1)) := by
    refine ⟨C.labels (-1), ?_, ?_⟩
    · simp [sets]
    · simp only [Nat.zero_add, sets, Finset.mem_insert, Finset.mem_singleton]
      right
      rw [← hclose]
      congr 1
      omega
  simpa only [Nat.zero_add] using
    C.quadrangulate_arc hG heven (m - 1) 0 (by omega) (by omega) (by omega) hadm

namespace Subdivision

variable {C} {x y : ℕ}

def cells : {x y : ℕ} → Subdivision C x y → ℕ
  | _, _, .edge _ => 0
  | _, _, .node _ Q₁ Q₂ Q₃ => 1 + Q₁.cells + Q₂.cells + Q₃.cells

def leaves : {x y : ℕ} → Subdivision C x y → ℕ
  | _, _, .edge _ => 1
  | _, _, .node _ Q₁ Q₂ Q₃ => Q₁.leaves + Q₂.leaves + Q₃.leaves

lemma cells_length (Q : Subdivision C x y) : 2 * Q.cells + 1 + x = y := by
  induction Q with
  | edge h => simp only [cells]; omega
  | node cell Q₁ Q₂ Q₃ h₁ h₂ h₃ => simp only [cells]; omega

lemma leaves_length (Q : Subdivision C x y) : Q.leaves + x = y := by
  induction Q with
  | edge h => simp only [leaves]; omega
  | node cell Q₁ Q₂ Q₃ h₁ h₂ h₃ => simp only [leaves]; omega

def interiorDiagonals (Q : Subdivision C x y) : ℕ := Q.cells - 1

lemma counts (hm : 4 ≤ m) (Q : Subdivision C 0 (m - 1)) :
    Q.cells = (m - 2) / 2 ∧ Q.interiorDiagonals = (m - 4) / 2 ∧
    Q.leaves = m - 1 := by
  have hc := Q.cells_length
  have hl := Q.leaves_length
  simp only [interiorDiagonals]
  omega

def sumCells : {x y : ℕ} → Subdivision C x y → (ℕ → ℕ → ℕ → ℕ → ℝ) → ℝ
  | _, _, .edge _, _ => 0
  | x, y, .node (p := p) (q := q) _ Q₁ Q₂ Q₃, localTerm =>
      localTerm x p q y + Q₁.sumCells localTerm + Q₂.sumCells localTerm + Q₃.sumCells localTerm

lemma signed_cancellation (Q : Subdivision C x y)
    (gain : ℕ → ℕ → ℝ) (localTerm : ℕ → ℕ → ℕ → ℕ → ℝ)
    (hshort : ∀ x, gain x (x + 1) = 0)
    (hcell : ∀ x p q y, C.Cell x p q y →
      gain x y = localTerm x p q y + gain x p + gain p q + gain q y) :
    gain x y = Q.sumCells localTerm := by
  induction Q with
  | edge h => simpa only [h, sumCells] using hshort _
  | node cell Q₁ Q₂ Q₃ h₁ h₂ h₃ =>
    simpa only [sumCells, h₁, h₂, h₃] using hcell _ _ _ _ cell

end Subdivision

end CycleData

end MatchingFPRAS.Cells

namespace MatchingFPRAS.Transport

variable {V E L : Type*}

namespace IndexedCycle

variable {inc : E → V → Prop} (c : IndexedCycle inc)

def zindex (i : ℤ) : Fin c.size :=
  ⟨(i % (c.size : ℤ)).toNat, (Int.toNat_lt (Int.emod_nonneg _ (by
    have := c.four_le; omega))).mpr (Int.emod_lt_of_pos _ (by have := c.four_le; omega))⟩

def vertexAtZ (i : ℤ) : V := c.vertex (c.zindex i)

def edgeAtZ (i : ℤ) : E := c.edge (c.zindex i)

lemma zindex_nat (i : ℕ) : c.zindex i = c.index i := by
  apply Fin.ext
  change ((i : ℤ) % (c.size : ℤ)).toNat = i % c.size
  rw [← Int.natCast_emod, Int.toNat_natCast]

lemma zindex_periodic (i : ℤ) : c.zindex (i + c.size) = c.zindex i := by
  apply Fin.ext
  simp [zindex]

lemma vertexAtZ_nat (i : ℕ) : c.vertexAtZ i = c.vertexAt i := by
  simp [vertexAtZ, vertexAt, c.zindex_nat]

lemma edgeAtZ_nat (i : ℕ) : c.edgeAtZ i = c.edgeAt i := by
  simp [edgeAtZ, edgeAt, c.zindex_nat]

lemma vertexAtZ_periodic (i : ℤ) : c.vertexAtZ (i + c.size) = c.vertexAtZ i := by
  simp [vertexAtZ, c.zindex_periodic]

lemma edgeAtZ_periodic (i : ℤ) : c.edgeAtZ (i + c.size) = c.edgeAtZ i := by
  simp [edgeAtZ, c.zindex_periodic]

lemma zindex_succ (i : ℤ) : c.zindex (i + 1) =
    ⟨((c.zindex i).val + 1) % c.size, Nat.mod_lt _ (by have := c.four_le; omega)⟩ := by
  have hsz : (c.size : ℤ) ≠ 0 := by have := c.four_le; omega
  apply Fin.ext
  apply Int.natCast_inj.mp
  change (((i + 1) % (c.size : ℤ)).toNat : ℤ) =
    (((((i % (c.size : ℤ)).toNat + 1) % c.size) : ℕ) : ℤ)
  rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hsz), Int.natCast_emod,
    Nat.cast_add, Nat.cast_one, Int.toNat_of_nonneg (Int.emod_nonneg _ hsz)]
  simp only [Int.add_emod, Int.emod_emod]

lemma edgeAtZ_incidence (i : ℤ) (v : V) :
    inc (c.edgeAtZ i) v ↔ v = c.vertexAtZ i ∨ v = c.vertexAtZ (i+1) := by
  simpa [edgeAtZ, vertexAtZ, c.zindex_succ] using c.incidence (c.zindex i) v

end IndexedCycle

namespace BagEdge

variable {bags : V → Finset L}

def color (e : BagEdge bags) : L := e.val.color

lemma color_mem (e : BagEdge bags) {v : V} (hv : e.Incident v) : e.color ∈ bags v :=
  e.property v hv

def ofEndpoints (v w : V) (hvw : v ≠ w) (l : L)
    (hlv : l ∈ bags v) (hlw : l ∈ bags w) : BagEdge bags :=
  ⟨⟨(s(v,w),l), by simpa using hvw⟩, by
    intro u hu
    change u ∈ s(v,w) at hu
    change l ∈ bags u
    rcases Sym2.mem_iff.mp hu with rfl | rfl
    · exact hlv
    · exact hlw⟩

lemma ofEndpoints_incidence (v w : V) (hvw : v ≠ w) (l : L)
    (hlv : l ∈ bags v) (hlw : l ∈ bags w) (u : V) :
    (ofEndpoints v w hvw l hlv hlw).Incident u ↔ u = v ∨ u = w :=
  Sym2.mem_iff

lemma ofEndpoints_color (v w : V) (hvw : v ≠ w) (l : L)
    (hlv : l ∈ bags v) (hlw : l ∈ bags w) :
    (ofEndpoints v w hvw l hlv hlw).color = l := rfl

end BagEdge

end MatchingFPRAS.Transport

end OAI
