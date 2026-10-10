import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarProgramBounds

namespace OAI

/-! Explicit indices of each extraction, scaling, and insertion pulse. These
are arithmetic indices into the actual compiled list, not choice functions. -/

namespace ForcedComputation.PlanarRouting

open ShearFlows

def blocks {α β : Type*} {k : ℕ} (l : List α) (f : α → Fin k → β) : List β :=
  l.flatMap (fun a => List.ofFn (f a))

theorem blocks_length {α β : Type*} {k : ℕ} (l : List α) (f : α → Fin k → β) :
    (blocks l f).length = l.length * k := by
  induction l with
  | nil => simp [blocks]
  | cons a l ih =>
      change (List.ofFn (f a) ++ blocks l f).length = (a :: l).length * k
      rw [List.length_append, List.length_ofFn, ih, List.length_cons]
      ring

theorem block_index_lt {m k i j : ℕ} (hi : i < m) (hj : j < k) : i * k + j < m * k := by
  calc
    i * k + j < i * k + k := Nat.add_lt_add_left hj _
    _ = (i + 1) * k := by ring
    _ ≤ m * k := Nat.mul_le_mul_right k hi

theorem blocks_get {α β : Type*} {k : ℕ} (l : List α) (f : α → Fin k → β)
    (i j : ℕ) (hi : i < l.length) (hj : j < k) :
    (blocks l f)[i * k + j]'(by rw [blocks_length]; exact block_index_lt hi hj) =
      f (l[i]'hi) ⟨j, hj⟩ := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a l ih =>
      cases i with
      | zero => simp [blocks, List.flatMap_cons, List.getElem_append_left, hj]
      | succ i =>
          have hi' : i < l.length := by simpa using hi
          simp only [blocks, List.flatMap_cons]
          rw [List.getElem_append_right (by simp; rw [Nat.succ_mul]; omega)]
          have he : (i + 1) * k + j - (List.ofFn (f a)).length = i * k + j := by
            simp only [List.length_ofFn, Nat.succ_mul]
            omega
          simp only [he, List.getElem_cons_succ]
          exact ih i hi'

theorem append_three_left {α : Type*} (l₀ l₁ l₂ : List α) (i : ℕ) (hi : i < l₀.length) :
    (l₀ ++ l₁ ++ l₂)[i]'(by simp only [List.length_append]; omega) = l₀[i]'hi := by
  rw [List.getElem_append_left (as := l₀ ++ l₁) (bs := l₂) (by simp only [List.length_append]; omega)]
  rw [List.getElem_append_left hi]

theorem append_three_middle {α : Type*} (l₀ l₁ l₂ : List α) (i : ℕ) (hi : i < l₁.length) :
    (l₀ ++ l₁ ++ l₂)[l₀.length + i]'(by simp only [List.length_append]; omega) = l₁[i]'hi := by
  rw [List.getElem_append_left (as := l₀ ++ l₁) (bs := l₂) (by simp only [List.length_append]; omega)]
  rw [List.getElem_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]

theorem append_three_right {α : Type*} (l₀ l₁ l₂ : List α) (i : ℕ) (hi : i < l₂.length) :
    (l₀ ++ l₁ ++ l₂)[l₀.length + l₁.length + i]'(by simp only [List.length_append]; omega) = l₂[i]'hi := by
  rw [List.getElem_append_right (as := l₀ ++ l₁) (bs := l₂) (by simp only [List.length_append]; omega)]
  simp only [List.length_append, Nat.add_sub_cancel_left]

end ForcedComputation.PlanarRouting

namespace ForcedComputation.Recorder.Planar

open ShearFlows PlanarRouting

deriving instance DecidableEq for Phase
instance (M : Alternating.Machine) (hM : M.WellFormed) : DecidableEq (Action M hM) :=
  fun a b => decidable_of_iff (a.owner = b.owner ∧ a.phase = b.phase)
    ⟨fun h => by
      cases a
      cases b
      rcases h with ⟨h₁, h₂⟩
      cases h₁
      cases h₂
      rfl,
    fun h => by cases h; exact ⟨rfl, rfl⟩⟩

def extractionBlock {M : Alternating.Machine} {hM : M.WellFormed}
    (b : Branch (finiteMachine M hM)) : Fin 2 → Action M hM :=
  ![⟨b, .extractHorizontal⟩, ⟨b, .extractVertical⟩]

def scalingBlock {M : Alternating.Machine} {hM : M.WellFormed}
    (b : Branch (finiteMachine M hM)) (k : Fin 4) : Action M hM := ⟨b, .scale k⟩

def insertionBlock {M : Alternating.Machine} {hM : M.WellFormed}
    (b : Branch (finiteMachine M hM)) : Fin 2 → Action M hM :=
  ![⟨b, .insertVertical⟩, ⟨b, .insertHorizontal⟩]

theorem actions_eq_blocks (M : Alternating.Machine) (hM : M.WellFormed) :
    actions M hM = blocks (sourceOrder M hM) extractionBlock ++
      blocks (geometricBranches M hM) scalingBlock ++ blocks (targetOrder M hM) insertionBlock := rfl

theorem actions_length (M : Alternating.Machine) (hM : M.WellFormed) :
    (actions M hM).length = 8 * (geometricBranches M hM).length := by
  rw [actions_eq_blocks]
  simp only [List.length_append, blocks_length,
    (sourceOrder_perm M hM).length_eq, (targetOrder_perm M hM).length_eq]
  omega

def sourceRank (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) : Fin (sourceOrder M hM).length :=
  ⟨(sourceOrder M hM).idxOf b, List.idxOf_lt_length_of_mem (sourceOrder_complete M hM b)⟩

def targetRank (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) : Fin (targetOrder M hM).length :=
  ⟨(targetOrder M hM).idxOf b, List.idxOf_lt_length_of_mem (targetOrder_complete M hM b)⟩

theorem sourceRank_get (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) : (sourceOrder M hM).get (sourceRank M hM b) = b :=
  List.idxOf_get _

theorem targetRank_get (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) : (targetOrder M hM).get (targetRank M hM b) = b :=
  List.idxOf_get _

def Action.index {M : Alternating.Machine} {hM : M.WellFormed} (a : Action M hM) : ℕ :=
  let n := (geometricBranches M hM).length
  match a.phase with
  | .extractHorizontal => 2 * (sourceRank M hM a.owner).val
  | .extractVertical => 2 * (sourceRank M hM a.owner).val + 1
  | .scale k => 2 * n + 4 * (branchIndex M hM a.owner).val + k.val
  | .insertVertical => 6 * n + 2 * (targetRank M hM a.owner).val
  | .insertHorizontal => 6 * n + 2 * (targetRank M hM a.owner).val + 1

theorem Action.index_lt {M : Alternating.Machine} {hM : M.WellFormed} (a : Action M hM) :
    a.index < (actions M hM).length := by
  have hs := (sourceRank M hM a.owner).isLt
  have ht := (targetRank M hM a.owner).isLt
  have hb := (branchIndex M hM a.owner).isLt
  have hslen := (sourceOrder_perm M hM).length_eq
  have htlen := (targetOrder_perm M hM).length_eq
  rw [actions_length]
  cases ha : a.phase with
  | scale k => have hk := k.isLt; simp only [Action.index, ha]; omega
  | _ => simp only [Action.index, ha]; omega

def extractionIndex (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) (k : Fin 2) : Fin (actions M hM).length :=
  ⟨2 * (sourceRank M hM b).val + k.val, by
    have hs := (sourceRank M hM b).isLt
    have hk := k.isLt
    have hslen := (sourceOrder_perm M hM).length_eq
    rw [actions_length]
    omega⟩

def scalingIndex (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) (k : Fin 4) : Fin (actions M hM).length :=
  ⟨2 * (geometricBranches M hM).length + 4 * (branchIndex M hM b).val + k.val, by
    have hb := (branchIndex M hM b).isLt
    have hk := k.isLt
    rw [actions_length]
    omega⟩

def insertionIndex (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) (k : Fin 2) : Fin (actions M hM).length :=
  ⟨6 * (geometricBranches M hM).length + 2 * (targetRank M hM b).val + k.val, by
    have hs := (targetRank M hM b).isLt
    have hk := k.isLt
    have hslen := (targetOrder_perm M hM).length_eq
    rw [actions_length]
    omega⟩

theorem extractionIndex_get (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) (k : Fin 2) :
    (actions M hM).get (extractionIndex M hM b k) = extractionBlock b k := by
  let s := sourceRank M hM b
  have hs : (sourceOrder M hM)[s.val]'s.isLt = b := sourceRank_get M hM b
  have hb := blocks_get (sourceOrder M hM) extractionBlock s.val k.val s.isLt k.isLt
  rw [hs] at hb
  have ht := append_three_left (blocks (sourceOrder M hM) extractionBlock)
    (blocks (geometricBranches M hM) scalingBlock) (blocks (targetOrder M hM) insertionBlock)
    (s.val * 2 + k.val) (by rw [blocks_length]; exact block_index_lt s.isLt k.isLt)
  rw [hb] at ht
  simpa only [actions_eq_blocks, extractionIndex, List.get_eq_getElem, Nat.mul_comm] using ht

theorem scalingIndex_get (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) (k : Fin 4) :
    (actions M hM).get (scalingIndex M hM b k) = scalingBlock b k := by
  let s := branchIndex M hM b
  have hs : (geometricBranches M hM)[s.val]'s.isLt = b := branchAt_index M hM b
  have hb := blocks_get (geometricBranches M hM) scalingBlock s.val k.val s.isLt k.isLt
  rw [hs] at hb
  have ht := append_three_middle (blocks (sourceOrder M hM) extractionBlock)
    (blocks (geometricBranches M hM) scalingBlock) (blocks (targetOrder M hM) insertionBlock)
    (s.val * 4 + k.val) (by rw [blocks_length]; exact block_index_lt s.isLt k.isLt)
  rw [hb] at ht
  simpa only [actions_eq_blocks, scalingIndex, List.get_eq_getElem, blocks_length,
    (sourceOrder_perm M hM).length_eq, Nat.mul_comm, Nat.add_assoc] using ht

theorem insertionIndex_get (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) (k : Fin 2) :
    (actions M hM).get (insertionIndex M hM b k) = insertionBlock b k := by
  let s := targetRank M hM b
  have hs : (targetOrder M hM)[s.val]'s.isLt = b := targetRank_get M hM b
  have hb := blocks_get (targetOrder M hM) insertionBlock s.val k.val s.isLt k.isLt
  rw [hs] at hb
  have ht := append_three_right (blocks (sourceOrder M hM) extractionBlock)
    (blocks (geometricBranches M hM) scalingBlock) (blocks (targetOrder M hM) insertionBlock)
    (s.val * 2 + k.val) (by rw [blocks_length]; exact block_index_lt s.isLt k.isLt)
  rw [hb] at ht
  have he : (sourceOrder M hM).length * 2 + (geometricBranches M hM).length * 4 +
      (s.val * 2 + k.val) = 6 * (geometricBranches M hM).length + 2 * s.val + k.val := by
    rw [(sourceOrder_perm M hM).length_eq]
    omega
  simpa only [actions_eq_blocks, insertionIndex, List.get_eq_getElem, blocks_length, he] using ht

end ForcedComputation.Recorder.Planar

end OAI
