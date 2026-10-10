import OAI.Algebra.DepthFive.Pairings

namespace OAI

namespace Problem335.Pairings

/-- The fixed labels at either external vertex. -/
def constantLabels {α : Type*} (a : α) : Labels α := ⟨a, a, a, a⟩

@[simp]
theorem respects_constantLabels {α : Type*} (τ : Kind) (a : α) :
    Respects τ (constantLabels a) := by
  cases τ <;> simp [Respects, constantLabels]

/-- Coordinates of the four paths in one layer are pairs of adjacent vertex labels. -/
def zipLabels {α β : Type*} (x : Labels α) (y : Labels β) : Labels (α × β) :=
  ⟨(x.p, y.p), (x.q, y.q), (x.r, y.r), (x.s, y.s)⟩

@[simp]
theorem respects_zipLabels {α β : Type*} (τ : Kind) (x : Labels α) (y : Labels β) :
    Respects τ (zipLabels x y) ↔ Respects τ x ∧ Respects τ y := by
  cases τ <;> simp only [Respects, zipLabels, Prod.mk.injEq] <;> tauto

/-- Add the two fixed external vertices to four paths specified by their internal labels. -/
def closePaths {α : Type*} {L : ℕ} (a : α) (x : Fin L → Labels α) :
    Fin (L + 2) → Labels α :=
  Fin.cases (constantLabels a) (Fin.lastCases (constantLabels a) x)

@[simp]
theorem closePaths_zero {α : Type*} {L : ℕ} (a : α) (x : Fin L → Labels α) :
    closePaths a x 0 = constantLabels a := rfl

@[simp]
theorem closePaths_last {α : Type*} {L : ℕ} (a : α) (x : Fin L → Labels α) :
    closePaths a x (Fin.last (L + 1)) = constantLabels a := by
  simp [closePaths, ← Fin.succ_last]

@[simp]
theorem closePaths_internal {α : Type*} {L : ℕ} (a : α)
    (x : Fin L → Labels α) (i : Fin L) :
    closePaths a x i.castSucc.succ = x i := by
  simp [closePaths]

/-- Layer constraints are exactly the independent constraints at internal vertices. -/
theorem closePaths_compatible_iff {α : Type*} {L : ℕ}
    (a : α) (τ : Fin (L + 1) → Kind) (x : Fin L → Labels α) :
    (∀ t : Fin (L + 1), Respects (τ t)
      (zipLabels (closePaths a x t.castSucc) (closePaths a x t.succ))) ↔
    ∀ i : Fin L, Respects (τ i.castSucc) (x i) ∧ Respects (τ i.succ) (x i) := by
  simp only [respects_zipLabels]
  constructor
  · intro h i
    constructor
    · simpa using (h i.castSucc).2
    · simpa only [Fin.castSucc_succ, closePaths_internal] using (h i.succ).1
  · intro h t
    constructor
    · refine Fin.cases ?_ (fun i => ?_) t
      · simp
      · simpa only [Fin.castSucc_succ, closePaths_internal] using (h i).2
    · refine Fin.lastCases ?_ (fun i => ?_) t
      · simp
      · simpa using (h i).1

/-- Four endpoint-fixed paths respecting a prescribed relaxed pairing in every layer. -/
abbrev RelaxedPaths (α : Type*) {L : ℕ} (a : α) (τ : Fin (L + 1) → Kind) :=
  {x : Fin L → Labels α // ∀ t : Fin (L + 1), Respects (τ t)
    (zipLabels (closePaths a x t.castSucc) (closePaths a x t.succ))}

/-- The explicit product decomposition used in the second trace count. -/
def relaxedPathsEquivAssignments (α : Type*) {L : ℕ}
    (a : α) (τ : Fin (L + 1) → Kind) :
    RelaxedPaths α a τ ≃ Assignments α τ where
  toFun x i := ⟨x.1 i, (closePaths_compatible_iff a τ x.1).mp x.2 i⟩
  invFun x := ⟨fun i => (x i).1,
    (closePaths_compatible_iff a τ _).mpr (fun i => (x i).2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact count of relaxed quadruples with fixed endpoints. -/
theorem card_relaxedPaths (α : Type*) [Fintype α] [DecidableEq α]
    {L : ℕ} (a : α) (τ : Fin (L + 1) → Kind) :
    Fintype.card (RelaxedPaths α a τ) =
      Fintype.card α ^ (2 * L - adjacentSwitches τ) :=
  (Fintype.card_congr (relaxedPathsEquivAssignments α a τ)).trans (card_assignments α τ)

/-- Boolean-word form of the count, with false = normal and true = diagonal. -/
theorem card_relaxedPaths_bool (α : Type*) [Fintype α] [DecidableEq α]
    {L : ℕ} (a : α) (τ : Fin (L + 1) → Bool) :
    Fintype.card (RelaxedPaths α a (fun i => boolKindEquiv (τ i))) =
      Fintype.card α ^ (2 * L - adjacentSwitches τ) := by
  rw [card_relaxedPaths, adjacentSwitches_comp_injective τ boolKindEquiv
    boolKindEquiv.injective]

end Problem335.Pairings

end OAI
