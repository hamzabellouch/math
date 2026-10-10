import OAI.RepresentationTheory.FoulkesHowe.SecondLabels

namespace OAI

noncomputable section
namespace Problem346.SecondTransfer

/-- Swap two factor positions in one nonzero row, leaving all other rows fixed. -/
def rowFactorSwap {r b : ℕ} (i : Fin r) (j l : Fin b) :
    Fin (r+1) → Equiv.Perm (Fin b) :=
  fun a => if a = i.succ then Equiv.swap j l else Equiv.refl _

/-- Changing any remaining source factor to the common block agrees with progressing
the prefix count, after a permutation internal to that row. -/
theorem update_label_eq_progress_rowSwap
    {r b : ℕ} (k : Fin r → ℕ) (i : Fin r) (hi : k i < b)
    (j : Fin b) (hj : k i ≤ j.val) (p : Fin (r+1) × Fin b) :
    Function.update (label k) (i.succ, j) none p =
      label (Function.update k i (k i+1))
        (p.1, rowFactorSwap i j ⟨k i, hi⟩ p.1 p.2) := by
  classical
  rcases p with ⟨a,l⟩
  refine Fin.cases ?_ (fun a => ?_) a
  · simp [Function.update, rowFactorSwap, label]
    intro h
    have hv := congrArg Fin.val h
    simp at hv
  · by_cases hai : a = i
    · subst a
      by_cases hlj : l = j
      · subst l
        simp [rowFactorSwap, label]
      · by_cases hlk : l = (⟨k i, hi⟩ : Fin b)
        · subst l
          have hjval : k i < j.val := by
            have hne : j.val ≠ k i := by
              intro he
              apply hlj
              exact Fin.ext he.symm
            omega
          simp [rowFactorSwap, label, hlj, Nat.not_lt.mpr (by omega : k i+1 ≤ j.val)]
        · have hval : l.val ≠ k i := by
            intro he
            apply hlk
            exact Fin.ext he
          have hlt : l.val < k i+1 ↔ l.val < k i := by omega
          simp [rowFactorSwap, label, hlj, hlt,
            Equiv.swap_apply_of_ne_of_ne hlj hlk]
    · simp [rowFactorSwap, label, hai]

/-- Any expression invariant under permutations of factors within each row takes the
same value on a derivative label update and the progressed prefix labels. -/
theorem invariant_update_label_eq_progress
    {r b : ℕ} {A : Type*}
    (F : ((Fin (r+1) × Fin b) → Block r) → A)
    (hF : ∀ (l : (Fin (r+1) × Fin b) → Block r)
      (σ : Fin (r+1) → Equiv.Perm (Fin b)),
      F (fun p => l (p.1, σ p.1 p.2)) = F l)
    (k : Fin r → ℕ) (i : Fin r) (hi : k i < b)
    (j : Fin b) (hj : k i ≤ j.val) :
    F (Function.update (label k) (i.succ,j) none) =
      F (label (Function.update k i (k i+1))) := by
  have heq : Function.update (label k) (i.succ,j) none =
      fun p => label (Function.update k i (k i+1))
        (p.1, rowFactorSwap i j ⟨k i, hi⟩ p.1 p.2) := by
    funext p
    exact update_label_eq_progress_rowSwap k i hi j hj p
  rw [heq]
  exact hF _ _

end Problem346.SecondTransfer

end

end OAI
