import OAI.Combinatorics.Ramsey.CycleClique.Construction.AssignedCutProfile

namespace OAI

/-! A representative replacement preserves all assigned amounts except
for the paths absorbed into its one new assigned path. -/

namespace CycleClique.Construction
open scoped Classical

variable {V : Type*} {Q : Finset V}

namespace AssignedCutProfile

theorem reassemble {A B : List V} {x : V} (X : AssignedCutProfile Q A x B)
    (hA : A ≠ []) {w : List ℕ} (h : AssignedAmounts Q A w) :
    AssignedAmounts Q (A ++ x :: B) (w ++ X.removed ++ X.after) := by
  rw [X.tail_eq, X.removed_eq]
  simpa [hA, List.append_assoc] using
    h.append_segment hA X.outside (X.lead_nonempty hA) X.after_profile

theorem merged {A B C D J : List V} {x y : V}
    (X : AssignedCutProfile Q A x B) (Y : AssignedCutProfile Q C y D)
    (hJ : ∀ z ∈ J, z ∉ Q) (hJne : J ≠ []) :
    AssignedAmounts Q (B.reverse ++ x :: (J ++ y :: D))
      (X.after.reverse ++ (J.length + (X.removed ++ Y.removed).sum) :: Y.after) := by
  let K := X.lead.reverse ++ J ++ Y.lead
  have hK : ∀ z ∈ K, z ∉ Q := by
    intro z hz
    simp only [K, List.mem_append, List.mem_reverse] at hz
    rcases hz with (hz | hz) | hz
    · exact X.outside z hz
    · exact hJ z hz
    · exact Y.outside z hz
  have hKne : K ≠ [] := by
    intro he
    have hn := congrArg List.length he
    simp only [K, List.length_append, List.length_reverse, List.length_nil] at hn
    have hpos := List.length_pos_iff.mpr hJne
    omega
  have hlen : K.length = J.length + (X.removed ++ Y.removed).sum := by
    simp only [K, List.length_append, List.length_reverse, List.sum_append,
      X.removed_sum, Y.removed_sum]
    omega
  have hh := X.after_profile.reverse.append_segment
    (by simp) hK hKne Y.after_profile
  have heq : B.reverse ++ x :: (J ++ y :: D) =
      (X.endpoint :: X.rest).reverse ++ K ++ Y.endpoint :: Y.rest := by
    have h0 : B.reverse ++ x :: (J ++ y :: D) = (x :: B).reverse ++ J ++ (y :: D) := by
      simp [List.append_assoc]
    rw [h0, X.tail_eq, Y.tail_eq]
    simp [K, List.reverse_append, List.append_assoc]
  rw [heq]
  simpa only [hlen] using hh

end AssignedCutProfile

theorem different_chain_profiles
    {P M R : List (List V)} {A B C D J : List V} {x y : V}
    (X : AssignedCutProfile Q A x B) (Y : AssignedCutProfile Q C y D)
    {wp wm wr : List ℕ} (hP : SystemAssignedAmounts Q P wp)
    (hM : SystemAssignedAmounts Q M wm) (hR : SystemAssignedAmounts Q R wr)
    (hJ : ∀ z ∈ J, z ∉ Q) (hJne : J ≠ []) :
    ∃ original output kept removed : List ℕ,
      SystemAssignedAmounts Q (P ++ (A ++ x :: B) :: M ++ (C ++ y :: D) :: R) original ∧
      SystemAssignedAmounts Q (P ++ A :: M ++ C :: (B.reverse ++ x :: (J ++ y :: D)) :: R) output ∧
      original.Perm (kept ++ removed) ∧
      output.Perm ((J.length + removed.sum) :: kept) := by
  let kept := wp ++ X.before ++ X.after ++ wm ++ Y.before ++ Y.after ++ wr
  let removed := X.removed ++ Y.removed
  let original := wp ++ (X.before ++ X.removed ++ X.after) ++ wm ++
    (Y.before ++ Y.removed ++ Y.after) ++ wr
  let output := wp ++ X.before ++ wm ++ Y.before ++ X.after.reverse ++
    (J.length + removed.sum) :: (Y.after ++ wr)
  refine ⟨original, output, kept, removed, ?_, ?_, ?_, ?_⟩
  · simpa only [original, List.append_assoc] using
      hP.append ((SystemAssignedAmounts.cons X.full_profile hM).append
        (.cons Y.full_profile hR))
  · simpa only [output, removed, List.append_assoc, List.cons_append] using
      hP.append ((SystemAssignedAmounts.cons X.before_profile hM).append
        (.cons Y.before_profile (.cons (X.merged Y hJ hJne) hR)))
  · apply List.perm_iff_count.mpr
    intro a
    simp only [original, kept, removed, List.count_append]
    omega
  · apply List.perm_iff_count.mpr
    intro a
    simp only [output, kept, List.count_append, List.count_cons, List.count_reverse]
    omega

theorem same_chain_profiles
    {P R : List (List V)} {A B D J : List V} {x y : V}
    (X : AssignedCutProfile Q A x B)
    (Y : AssignedCutProfile Q (A ++ x :: B) y D)
    {wp wr : List ℕ} (hP : SystemAssignedAmounts Q P wp)
    (hR : SystemAssignedAmounts Q R wr)
    (hJ : ∀ z ∈ J, z ∉ Q) (hJne : J ≠ []) :
    ∃ original output kept removed : List ℕ,
      SystemAssignedAmounts Q (P ++ (A ++ (x :: B) ++ y :: D) :: R) original ∧
      SystemAssignedAmounts Q (P ++ A :: (B.reverse ++ x :: (J ++ y :: D)) :: R) output ∧
      original.Perm (kept ++ removed) ∧
      output.Perm ((J.length + removed.sum) :: kept) := by
  let kept := wp ++ X.before ++ X.after ++ Y.after ++ wr
  let removed := X.removed ++ Y.removed
  let original := wp ++ (X.before ++ X.removed ++ X.after ++ Y.removed ++ Y.after) ++ wr
  let output := wp ++ X.before ++ X.after.reverse ++
    (J.length + removed.sum) :: (Y.after ++ wr)
  refine ⟨original, output, kept, removed, ?_, ?_, ?_, ?_⟩
  · have hh := Y.reassemble (by simp) X.full_profile
    simpa only [original, List.append_assoc] using hP.append (.cons hh hR)
  · simpa only [output, removed, List.append_assoc, List.cons_append] using
      hP.append (.cons X.before_profile (.cons (X.merged Y hJ hJne) hR))
  · apply List.perm_iff_count.mpr
    intro a
    simp only [original, kept, removed, List.count_append]
    omega
  · apply List.perm_iff_count.mpr
    intro a
    simp only [output, kept, List.count_append, List.count_cons, List.count_reverse]
    omega

end CycleClique.Construction

end OAI
