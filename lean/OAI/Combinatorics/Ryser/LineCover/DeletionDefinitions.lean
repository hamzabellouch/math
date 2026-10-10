import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Union

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover

variable {P : Type*} [DecidableEq P]

abbrev Outcome (shapes : Finset (Finset P)) (D : ℕ) :=
  {A : Finset ↥shapes // A.card ≤ D}

def emptyOutcome (shapes : Finset (Finset P)) (D : ℕ) : Outcome shapes D :=
  ⟨∅, by simp⟩

variable {shapes : Finset (Finset P)} {D n : ℕ}

def deleted (ignore : Finset (Finset P)) (a : Outcome shapes D) : Finset P :=
  (a.val.filter (fun L => L.val ∉ ignore)).biUnion Subtype.val

@[simp] theorem mem_deleted {ignore : Finset (Finset P)}
    {a : Outcome shapes D} {x : P} :
    x ∈ deleted ignore a ↔ ∃ L ∈ a.val, L.val ∉ ignore ∧ x ∈ L.val := by
  simp [deleted, Finset.mem_biUnion, and_assoc]

@[simp] theorem deleted_emptyOutcome (ignore : Finset (Finset P)) :
    deleted ignore (emptyOutcome shapes D) = ∅ := by
  simp [deleted, emptyOutcome]

def selected (ω : Fin n → Outcome shapes D) : Finset (Finset P) :=
  Finset.univ.biUnion (fun i => (ω i).val.image Subtype.val)

@[simp] theorem mem_selected {ω : Fin n → Outcome shapes D} {L : Finset P} :
    L ∈ selected ω ↔ ∃ i, ∃ s ∈ (ω i).val, s.val = L := by
  simp [selected, Finset.mem_biUnion, Finset.mem_image]

variable [instFintypeP : Fintype P]

def survivors (ignore : Finset (Finset P))
    (ω : Fin n → Outcome shapes D) : Finset P :=
  Finset.univ \ Finset.univ.biUnion (fun i => deleted ignore (ω i))

@[simp] theorem mem_survivors {ignore : Finset (Finset P)}
    {ω : Fin n → Outcome shapes D} {x : P} :
    x ∈ survivors ignore ω ↔ ∀ i, x ∉ deleted ignore (ω i) := by
  simp [survivors, Finset.mem_biUnion]

theorem mem_survivors_active {ignore : Finset (Finset P)}
    {ω : Fin n → Outcome shapes D} {x : P} :
    x ∈ survivors ignore ω ↔ ∀ L ∈ selected ω \ ignore, x ∉ L := by
  rw [mem_survivors]
  constructor
  · intro h L hL hxL
    rcases Finset.mem_sdiff.mp hL with ⟨hsel, hI⟩
    rcases mem_selected.mp hsel with ⟨i, s, hs, rfl⟩
    exact h i (mem_deleted.mpr ⟨s, hs, hI, hxL⟩)
  · intro h i hx
    rcases mem_deleted.mp hx with ⟨s, hs, hI, hxs⟩
    exact h s.val (Finset.mem_sdiff.mpr
      ⟨mem_selected.mpr ⟨i, s, hs, rfl⟩, hI⟩) hxs

theorem survivors_mono_ignore {ignore larger : Finset (Finset P)}
    (h : ignore ⊆ larger) (ω : Fin n → Outcome shapes D) :
    survivors ignore ω ⊆ survivors larger ω := by
  intro x hx
  apply mem_survivors.mpr
  intro i hxi
  rcases mem_deleted.mp hxi with ⟨s, hs, hnot, hxs⟩
  exact mem_survivors.mp hx i
    (mem_deleted.mpr ⟨s, hs, fun hI => hnot (h hI), hxs⟩)

theorem survivors_insert_eq_of_not_selected
    {ignore : Finset (Finset P)} {ω : Fin n → Outcome shapes D}
    {L : Finset P} (hL : L ∉ selected ω) :
    survivors (insert L ignore) ω = survivors ignore ω := by
  ext x
  rw [mem_survivors_active, mem_survivors_active,
    Finset.sdiff_insert_of_notMem hL ignore]

theorem selected_of_survivors_insert_ne
    {ignore : Finset (Finset P)} {ω : Fin n → Outcome shapes D}
    {L : Finset P} (changed : survivors (insert L ignore) ω ≠ survivors ignore ω) :
    L ∈ selected ω := by
  by_contra hL
  exact changed (survivors_insert_eq_of_not_selected hL)

theorem not_ignored_of_survivors_insert_ne
    {ignore : Finset (Finset P)} {ω : Fin n → Outcome shapes D}
    {L : Finset P} (changed : survivors (insert L ignore) ω ≠ survivors ignore ω) :
    L ∉ ignore := by
  intro hL
  exact changed (by rw [Finset.insert_eq_of_mem hL])

def cleanCover (ignore : Finset (Finset P)) (ω : Fin n → Outcome shapes D)
    (cover : Finset (Finset P)) : Finset (Finset P) :=
  cover \ (selected ω \ ignore)

theorem survivors_inter_cleanCover (ignore : Finset (Finset P))
    (ω : Fin n → Outcome shapes D) (cover : Finset (Finset P)) :
    survivors ignore ω ∩ cover.biUnion id =
      survivors ignore ω ∩ (cleanCover ignore ω cover).biUnion id := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_inter.mp hx with ⟨hs, hc⟩
    rcases Finset.mem_biUnion.mp hc with ⟨L, hLc, hxL⟩
    refine Finset.mem_inter.mpr ⟨hs,
      Finset.mem_biUnion.mpr ⟨L, ?_, hxL⟩⟩
    change L ∈ cover \ (selected ω \ ignore)
    exact Finset.mem_sdiff.mpr ⟨hLc,
      fun hL => mem_survivors_active.mp hs L hL hxL⟩
  · intro hx
    rcases Finset.mem_inter.mp hx with ⟨hs, hc⟩
    rcases Finset.mem_biUnion.mp hc with ⟨L, hLc, hxL⟩
    change L ∈ cover \ (selected ω \ ignore) at hLc
    exact Finset.mem_inter.mpr ⟨hs,
      Finset.mem_biUnion.mpr ⟨L, (Finset.mem_sdiff.mp hLc).1, hxL⟩⟩

theorem cleanCover_covers {ignore : Finset (Finset P)}
    {ω : Fin n → Outcome shapes D} {cover : Finset (Finset P)}
    (h : survivors ignore ω ⊆ cover.biUnion id) :
    survivors ignore ω ⊆ (cleanCover ignore ω cover).biUnion id := by
  intro x hx
  have hh := Finset.mem_inter.mpr ⟨hx, h hx⟩
  rw [survivors_inter_cleanCover] at hh
  exact (Finset.mem_inter.mp hh).2

theorem cleanCover_card_le (ignore : Finset (Finset P))
    (ω : Fin n → Outcome shapes D) (cover : Finset (Finset P)) :
    (cleanCover ignore ω cover).card ≤ cover.card := let _ := instFintypeP;
  Finset.card_le_card Finset.sdiff_subset

end RyserCoveringCounterexample.LineCover

end

end OAI
