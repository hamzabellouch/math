import OAI.Combinatorics.MatrixRemoval.Host
import OAI.Combinatorics.MatrixRemoval.ThreeSeedSampling

namespace OAI

/-!
The canonical host projections and protected-cell sampling bridge.
Three seeds give the cellwise sampling bound.
-/

namespace Problem348.Construction.HostSampling

open Problem348.TreeSampling

/-- Anchor and dummy positions use their independent axis seed. -/
def sampleDepth {h : ℕ} : Position h → Option (Fin (h + 1))
  | Sum.inl _ => none
  | Sum.inr (Sum.inl v) => some ⟨depth v, Nat.lt_succ_of_le (depth_le v)⟩
  | Sum.inr (Sum.inr _) => none

/-- The coordinate within the size-`2^h` class of a raw host position. -/
def offset {h : ℕ} : Position h → Fin (2 ^ h)
  | Sum.inl (_, _, x) => x
  | Sum.inr (Sum.inl v) => v.2
  | Sum.inr (Sum.inr x) => x

/-- The selected coordinate in the class containing a given position. -/
def coordinate {h : ℕ} (z u : Fin (2 ^ h)) : Position h → Fin (2 ^ h)
  | Sum.inl _ => u
  | Sum.inr (Sum.inl v) => atLevel h (depth v) (depth_le v) z u
  | Sum.inr (Sum.inr _) => u

/-- Whether both positions of a fixed raw cell are selected. -/
def Selected {h : ℕ} (s : Seeds (2 ^ h)) (r c : Position h) : Prop :=
  (coordinate s.1 s.2.1 r, coordinate s.1 s.2.2 c) = (offset r, offset c)

instance {h : ℕ} (s : Seeds (2 ^ h)) (r c : Position h) :
    Decidable (Selected s r c) := inferInstanceAs (Decidable (_ = _))

/-- Protected cells: at least one anchor/dummy position, or two root positions. -/
def Protected {h : ℕ} (r c : Position h) : Prop :=
  sampleDepth r = none ∨ sampleDepth c = none ∨
    sampleDepth r = some ⟨0, by omega⟩ ∧ sampleDepth c = some ⟨0, by omega⟩

@[simp] theorem protected_anchor_left {h : ℕ} (a : AnchorPosition h)
    (c : Position h) : Protected (Sum.inl a) c := by
  simp [Protected, sampleDepth]

@[simp] theorem protected_anchor_right {h : ℕ} (r : Position h)
    (a : AnchorPosition h) : Protected r (Sum.inl a) := by
  simp [Protected, sampleDepth]

@[simp] theorem protected_dummy_left {h : ℕ} (x : Fin (2 ^ h))
    (c : Position h) : Protected (Sum.inr (Sum.inr x)) c := by
  simp [Protected, sampleDepth]

@[simp] theorem protected_dummy_right {h : ℕ} (r : Position h)
    (x : Fin (2 ^ h)) : Protected r (Sum.inr (Sum.inr x)) := by
  simp [Protected, sampleDepth]

 theorem protected_roots {h : ℕ} (v w : VariablePosition h)
    (hv : depth v = 0) (hw : depth w = 0) :
    Protected (Sum.inr (Sum.inl v)) (Sum.inr (Sum.inl w)) := by
  simp [Protected, sampleDepth, hv, hw]

/-- Concrete host protected-cell events all have exactly `2^h` seed preimages. -/
theorem selected_fiber_card {h : ℕ} (r c : Position h) (hp : Protected r c) :
    Fintype.card {s : Seeds (2 ^ h) // Selected s r c} = 2 ^ h := by
  rcases r with ⟨t, u, x⟩ | (v | x) <;>
    rcases c with ⟨t', u', y⟩ | (w | y)
  · exact card_both_fiber x y
  · exact card_atLevel_column_fiber h (depth w) (depth_le w) x w.2
  · exact card_both_fiber x y
  · exact card_atLevel_row_fiber h (depth v) (depth_le v) v.2 y
  · have hd : depth v = 0 ∧ depth w = 0 := by
      simpa [Protected, sampleDepth, Fin.ext_iff] using hp
    have he : ∀ s : Seeds (2 ^ h), Selected s (Sum.inr (Sum.inl v))
        (Sum.inr (Sum.inl w)) ↔ s.2 = (v.2, w.2) := by
      intro s
      simp [Selected, coordinate, offset, hd.1, hd.2]
    calc
      _ = Fintype.card {s : Seeds (2 ^ h) // s.2 = (v.2, w.2)} :=
        Fintype.card_congr (Equiv.subtypeEquivRight he)
      _ = _ := card_both_fiber v.2 w.2
  · exact card_atLevel_row_fiber h (depth v) (depth_le v) v.2 y
  · exact card_both_fiber x y
  · exact card_atLevel_column_fiber h (depth w) (depth_le w) x w.2
  · exact card_both_fiber x y

/-- Fraction-free marginal equality, directly consumable by finite avoidance. -/
theorem selected_fiber_card_mul {h : ℕ} (r c : Position h) (hp : Protected r c) :
    Fintype.card {s : Seeds (2 ^ h) // Selected s r c} * (2 ^ h) ^ 2 =
      Fintype.card (Seeds (2 ^ h)) := by
  rw [selected_fiber_card r c hp, card_seeds]
  ring

/-- The same marginal in the `Finset.filter` form used by the union bound. -/
theorem selected_filter_card {h : ℕ} (r c : Position h) (hp : Protected r c) :
    (Finset.univ.filter fun s : Seeds (2 ^ h) => Selected s r c).card = 2 ^ h := by
  simpa only [Fintype.card_subtype] using selected_fiber_card r c hp

/-- A subset of the protected event has at most the same frequency. -/
theorem protected_event_card_le {h : ℕ} (r c : Position h)
    (event : Finset (Seeds (2 ^ h)))
    (hevent : ∀ s ∈ event, Protected r c ∧ Selected s r c) :
    event.card ≤ 2 ^ h := by
  classical
  rcases event.eq_empty_or_nonempty with hempty | ⟨s, hs⟩
  · simp [hempty]
  · have hp := (hevent s hs).1
    calc
      event.card ≤ (Finset.univ.filter fun s => Selected s r c).card := by
        apply Finset.card_le_card
        intro t ht
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact (hevent t ht).2
      _ = _ := selected_filter_card r c hp

/-- Guard-cell containment in the protected selected-cell event implies
the union-bound frequency estimate for each fixed raw cell. -/
theorem guard_frequency {h : ℕ}
    (guards : Seeds (2 ^ h) → Finset (Position h × Position h))
    (hguards : ∀ s rc, rc ∈ guards s →
      Protected rc.1 rc.2 ∧ Selected s rc.1 rc.2)
    (rc : Position h × Position h) :
    (Finset.univ.filter fun s => rc ∈ guards s).card * (2 ^ h) ^ 2 ≤
      Fintype.card (Seeds (2 ^ h)) := by
  classical
  have hb := protected_event_card_le rc.1 rc.2
    (Finset.univ.filter fun s => rc ∈ guards s)
    (fun s hs => hguards s rc (Finset.mem_filter.mp hs).2)
  rw [card_seeds]
  calc
    _ ≤ 2 ^ h * (2 ^ h) ^ 2 := Nat.mul_le_mul_right _ hb
    _ = (2 ^ h) ^ 3 := by ring

/-- Independent row and column reindexings preserve the protected-cell bound. -/
theorem transported_guard_frequency {h n : ℕ}
    (row col : Position h ≃ Fin n)
    (guards : Seeds (2 ^ h) → Finset (Fin n × Fin n))
    (hguards : ∀ s rc, rc ∈ guards s →
      Protected (row.symm rc.1) (col.symm rc.2) ∧
      Selected s (row.symm rc.1) (col.symm rc.2))
    (rc : Fin n × Fin n) :
    (Finset.univ.filter fun s => rc ∈ guards s).card * (2 ^ h) ^ 2 ≤
      Fintype.card (Seeds (2 ^ h)) := by
  classical
  have hb := protected_event_card_le (row.symm rc.1) (col.symm rc.2)
    (Finset.univ.filter fun s => rc ∈ guards s)
    (fun s hs => hguards s rc (Finset.mem_filter.mp hs).2)
  rw [card_seeds]
  calc
    _ ≤ 2 ^ h * (2 ^ h) ^ 2 := Nat.mul_le_mul_right _ hb
    _ = (2 ^ h) ^ 3 := by ring

end Problem348.Construction.HostSampling

end OAI
