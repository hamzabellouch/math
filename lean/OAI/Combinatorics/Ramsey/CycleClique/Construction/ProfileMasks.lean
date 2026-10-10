import OAI.Combinatorics.Ramsey.CycleClique.Construction.PathProfiles

namespace OAI

/-! A positive amount profile determines exactly which positions in each
chain belong to the clique. This is the interface to finite indexed models. -/

namespace CycleClique.Construction
variable {V : Type*} {Q : Finset V}

def profileMask : List ℕ → List Bool
  | [] => [true]
  | a :: w => true :: (List.replicate a false ++ profileMask w)

noncomputable def cliqueMask (Q : Finset V) (l : List V) : List Bool := by
  classical
  exact l.map (fun v => decide (v ∈ Q))

theorem cliqueMask_eq_map [DecidableEq V] (Q : Finset V) (l : List V) :
    cliqueMask Q l = l.map (fun v => decide (v ∈ Q)) := by
  unfold cliqueMask
  congr 1
  funext v
  exact congrArg (fun h => @decide (v ∈ Q) h) (Subsingleton.elim _ _)

theorem AssignedAmounts.mask {l : List V} {w : List ℕ}
    (h : AssignedAmounts Q l w) (hne : l ≠ []) : cliqueMask Q l = profileMask w := by
  classical
  induction h with
  | nil => exact False.elim (hne rfl)
  | singleton hx => simp [cliqueMask, profileMask, hx]
  | @step x y J B w hx hy hJ hJne ht ih =>
    have hmap : J.map (fun v => decide (v ∈ Q)) = List.replicate J.length false := by
      apply List.map_eq_replicate_iff.mpr
      intro v hv
      simp [hJ v hv]
    have htail := ih (by simp)
    simpa only [cliqueMask, List.map_cons, List.map_append, hx, decide_true,
      hmap, profileMask] using congrArg (fun L => true :: (List.replicate J.length false ++ L)) htail

theorem profileMask_length (w : List ℕ) :
    (profileMask w).length = w.sum + w.length + 1 := by
  induction w with
  | nil => rfl
  | cons a w ih => simp only [profileMask, List.length_cons, List.length_append,
      List.length_replicate, List.sum_cons, ih]; omega

theorem AssignedAmounts.nonempty_length_eq {l : List V} {w : List ℕ}
    (h : AssignedAmounts Q l w) (hne : l ≠ []) : l.length = w.sum + w.length + 1 := by
  have hh := congrArg List.length (h.mask hne)
  simpa only [cliqueMask, List.length_map, profileMask_length] using hh

theorem profiles_masks {C : List (List V)} {P : List (List ℕ)}
    (hp : List.Forall₂ (AssignedAmounts Q) C P) (hne : ∀ l ∈ C, l ≠ []) :
    C.map (cliqueMask Q) = P.map profileMask := by
  induction hp with
  | nil => rfl
  | @cons l w C P hw ht ih =>
    simp only [List.map_cons]
    rw [hw.mask (hne l (by simp)), ih (fun l hl => hne l (by simp [hl]))]

theorem profiles_lengths {C : List (List V)} {P : List (List ℕ)}
    (hp : List.Forall₂ (AssignedAmounts Q) C P) (hne : ∀ l ∈ C, l ≠ []) :
    C.map List.length = P.map (fun w => w.sum + w.length + 1) := by
  induction hp with
  | nil => rfl
  | @cons l w C P hw ht ih =>
    simp only [List.map_cons]
    rw [hw.nonempty_length_eq (hne l (by simp)), ih (fun l hl => hne l (by simp [hl]))]

end CycleClique.Construction

end OAI
