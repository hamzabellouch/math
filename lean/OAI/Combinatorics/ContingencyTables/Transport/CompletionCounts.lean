import OAI.Combinatorics.ContingencyTables.Sampling.PaddedCompletions

namespace OAI

/-!
# The literal zero-penalty sum counts residual completions

Finite balanced large-cell assignments are represented by bounded natural
matrices supported on the large cells. The zero-penalty predicate is
equivalent to the actual padded residual table equations. An explicit
entry bound proves when the formal capacities exclude no completion.
-/

namespace ContingencyTables.CompletionCounts

open scoped BigOperators Classical
open RowColumnPenalties PaddedCompletions NestedPenaltyApplication

variable {I J : Type*} [Fintype I] [Fintype J]

def LargeCompletion (small : I → J → Bool) (R : I → ℕ) (C : J → ℕ) :=
  {A : Table R C // Supported small A.val}

noncomputable instance largeCompletionFintype (small : I → J → Bool) (R : I → ℕ) (C : J → ℕ) :
    Fintype (LargeCompletion small R C) := by
  unfold LargeCompletion
  infer_instance

def Assignment (small : I → J → Bool) (B : I → J → ℕ) :=
  {a : (i : I) → (j : J) → Fin (B i j+1) // ∀ i j, small i j=true → (a i j).val=0}

noncomputable instance assignmentFintype (small : I → J → Bool) (B : I → J → ℕ) :
    Fintype (Assignment small B) := by
  unfold Assignment
  infer_instance

def assignmentMatrix {small : I → J → Bool} {B : I → J → ℕ} (a : Assignment small B) : I → J → ℕ :=
  fun i j => (a.val i j).val

omit [Fintype I] [Fintype J] in
lemma assignment_supported {small : I → J → Bool} {B : I → J → ℕ} (a : Assignment small B) :
    Supported small (assignmentMatrix a) := a.property

omit [Fintype I] [Fintype J] in
lemma assignment_bounded {small : I → J → Bool} {B : I → J → ℕ} (a : Assignment small B) (i : I) (j : J) :
    assignmentMatrix a i j ≤ B i j := Nat.le_of_lt_succ (a.val i j).isLt

noncomputable def fullPenalty (small : I → J → Bool) (B X Y A : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) : ℝ :=
  penalty cellLine (smallCoordinate small)
    (fullOffset B (fun i => r i+rowLargeCount small i*L) (fun j => c j+columnLargeCount small j*L))
    viewSlope (smallOffset small B r c) viewSlope (profile small B X Y A)

def ZeroAssignments (small : I → J → Bool) (B X Y : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) :=
  {a : Assignment small B // fullPenalty small B X Y (assignmentMatrix a) r c L=0}

noncomputable instance zeroAssignmentsFintype (small : I → J → Bool) (B X Y : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) : Fintype (ZeroAssignments small B X Y r c L) := by
  unfold ZeroAssignments
  infer_instance

/-- The total padded residual mass is at most the original mass plus
one padding unit L for each large cell. -/
theorem padded_total_le (small : I → J → Bool) (X : I → J → ℕ) (r : I → ℕ) (L : ℕ) :
    (∑ i, (r i-smallRow small X i+rowLargeCount small i*L)) ≤
      (∑ i, r i)+(∑ i, rowLargeCount small i)*L := by
  rw [Finset.sum_add_distrib,Finset.sum_mul]
  exact Nat.add_le_add_right (Finset.sum_le_sum (fun i _ => Nat.sub_le _ _)) _

/-- This is the exact reason the paper's formal large capacity excludes
no padded completion. No large-range enumeration is used. -/
theorem capacity_excludes_none (small : I → J → Bool) (B X : I → J → ℕ)
    (r : I → ℕ) (L d C : ℕ) (hcount : (∑ i, rowLargeCount small i) ≤ d)
    (hC : (∑ i, r i)+d*L ≤ C) (hB : ∀ i j, small i j=false → B i j=C) :
    ∀ i j, small i j=false →
      (∑ k, (r k-smallRow small X k+rowLargeCount small k*L)) ≤ B i j := by
  intro i j hij
  rw [hB i j hij]
  exact (padded_total_le small X r L).trans
    ((Nat.add_le_add_left (Nat.mul_le_mul_right L hcount) _).trans hC)

theorem large_count_le_dimension (small : I → J → Bool) :
    (∑ i, rowLargeCount small i) ≤ Fintype.card I*Fintype.card J := by
  calc
    _ ≤ ∑ _ : I, Fintype.card J := by
      apply Finset.sum_le_sum
      intro i _
      unfold rowLargeCount
      calc
        _ ≤ ∑ _ : J, (1:ℕ) := by
          apply Finset.sum_le_sum
          intro j _
          split_ifs <;> omega
        _ = Fintype.card J := by simp
    _ = _ := by simp

noncomputable def paperCapacity (small : I → J → Bool) (r : I → ℕ) (d L U : ℕ) : I → J → ℕ :=
  fun i j => if small i j then U else (∑ k, r k)+d*L+U+2

/-- For the manuscript's exact C=N+dL+U+2, the capacity hypothesis of
the count equivalence follows just from the dimension allowance. -/
theorem paper_capacity_excludes_none (small : I → J → Bool) (X : I → J → ℕ)
    (r : I → ℕ) (d L U : ℕ) (hd : Fintype.card I*Fintype.card J ≤ d) :
    ∀ i j, small i j=false →
      (∑ k, (r k-smallRow small X k+rowLargeCount small k*L)) ≤ paperCapacity small r d L U i j := by
  apply capacity_excludes_none small (paperCapacity small r d L U) X r L d
    ((∑ k, r k)+d*L+U+2) ((large_count_le_dimension small).trans hd)
  · omega
  · intro i j hij
    simp [paperCapacity,hij]

def firstPaperSmall (r : I → ℕ) (c : J → ℕ) (U : ℕ) (i : I) (j : J) : Bool :=
  decide (r i<U ∨ c j<U)

omit [Fintype I] [Fintype J] in
/-- Thus the large set is exactly the complete large-margin rectangle. -/
lemma firstPaperSmall_false_iff (r : I → ℕ) (c : J → ℕ) (U : ℕ) (i : I) (j : J) :
    firstPaperSmall r c U i j=false ↔ U ≤ r i ∧ U ≤ c j := by
  simp [firstPaperSmall]

noncomputable def dimensionAllowance : ℕ :=
  10+(Fintype.card I+1)*(Fintype.card J+1)

lemma dimension_le_allowance : Fintype.card I*Fintype.card J ≤ dimensionAllowance (I := I) (J := J) := by
  unfold dimensionAllowance
  nlinarith

noncomputable def completionEquiv (small : I → J → Bool) (B X Y : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    (hX : ∀ i j, small i j=true → X i j ≤ B i j)
    (hY : ∀ i j, small i j=true → Y i j ≤ B i j)
    (hres : OriginalResidualsNonnegative small B X Y r c)
    (hB : ∀ i j, small i j=false → (∑ k, (r k-smallRow small X k+rowLargeCount small k*L)) ≤ B i j) :
    ZeroAssignments small B X Y r c L ≃
      LargeCompletion small (fun i => r i-smallRow small X i+rowLargeCount small i*L)
        (fun j => c j-smallColumn small B Y j+columnLargeCount small j*L) where
  toFun a := ⟨⟨assignmentMatrix a.val,
    ((zero_penalty_iff_padded_completion small B X Y (assignmentMatrix a.val) r c L
      (assignment_supported a.val) hX hY (fun i j _ => assignment_bounded a.val i j)).mp a.property).2⟩,
    assignment_supported a.val⟩
  invFun A := by
    have hcap : ∀ i j, A.val.val i j ≤ B i j := by
      intro i j
      cases hs : small i j
      · exact (entry_le_total A.val.property i j).trans (hB i j hs)
      · rw [A.property i j hs]
        exact Nat.zero_le _
    let a : Assignment small B := ⟨fun i j => ⟨A.val.val i j,Nat.lt_succ_of_le (hcap i j)⟩,
      A.property⟩
    refine ⟨a,?_⟩
    exact (zero_penalty_iff_padded_completion small B X Y A.val.val r c L A.property hX hY
      (fun i j _ => hcap i j)).mpr ⟨hres,A.val.property⟩
  left_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    funext i j
    apply Fin.ext
    rfl
  right_inv A := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- The finite hard marginal is exactly the padded completion count;
if an original residual is negative every zero-penalty term vanishes. -/
theorem hard_count_eq (small : I → J → Bool) (B X Y : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    (hX : ∀ i j, small i j=true → X i j ≤ B i j)
    (hY : ∀ i j, small i j=true → Y i j ≤ B i j)
    (hB : ∀ i j, small i j=false → (∑ k, (r k-smallRow small X k+rowLargeCount small k*L)) ≤ B i j) :
    (∑ a : Assignment small B, if fullPenalty small B X Y (assignmentMatrix a) r c L=0 then (1:ℝ) else 0) =
      if OriginalResidualsNonnegative small B X Y r c then
        (Fintype.card (LargeCompletion small (fun i => r i-smallRow small X i+rowLargeCount small i*L)
          (fun j => c j-smallColumn small B Y j+columnLargeCount small j*L)):ℝ) else 0 := by
  by_cases hres : OriginalResidualsNonnegative small B X Y r c
  · rw [ite_eq_left hres]
    calc
      _ = (Fintype.card (ZeroAssignments small B X Y r c L):ℝ) := by
        rw [Finset.sum_boole,← Fintype.card_subtype]
        exact congrArg (fun n : ℕ => (n:ℝ)) (Fintype.card_congr
          (α := {a : Assignment small B // fullPenalty small B X Y (assignmentMatrix a) r c L=0})
          (β := ZeroAssignments small B X Y r c L) (Equiv.refl _))
      _ = _ := congrArg (fun n : ℕ => (n:ℝ))
        (Fintype.card_congr (completionEquiv small B X Y r c L hX hY hres hB))
  · rw [ite_eq_right hres]
    apply Finset.sum_eq_zero
    intro a _
    apply ite_eq_right
    intro hz
    exact hres ((zero_penalty_iff_padded_completion small B X Y (assignmentMatrix a) r c L
      (assignment_supported a) hX hY (fun i j _ => assignment_bounded a i j)).mp hz).1

/-- The first manuscript's actual supported padded-completion weight,
with its dimension allowance, padding, threshold and formal capacity. -/
noncomputable def firstPaperWeight (r : I → ℕ) (c : J → ℕ) (X Y : I → J → ℕ) : ℝ :=
  let d := dimensionAllowance (I := I) (J := J)
  let L := d^12
  let U := d^20
  let small := firstPaperSmall r c U
  let B := paperCapacity small r d L U
  if OriginalResidualsNonnegative small B X Y r c then
    (Fintype.card (LargeCompletion small (fun i => r i-smallRow small X i+rowLargeCount small i*L)
      (fun j => c j-smallColumn small B Y j+columnLargeCount small j*L)):ℝ) else 0

noncomputable def firstPaperHardSum (r : I → ℕ) (c : J → ℕ) (X Y : I → J → ℕ) : ℝ :=
  let d := dimensionAllowance (I := I) (J := J)
  let L := d^12
  let U := d^20
  let small := firstPaperSmall r c U
  let B := paperCapacity small r d L U
  ∑ a : Assignment small B, if fullPenalty small B X Y (assignmentMatrix a) r c L=0 then 1 else 0

/-- This identifies the actual finite zero-penalty large-assignment sum
with the original supported completion count, on every small profile. -/
theorem firstPaperHardSum_eq_weight (r : I → ℕ) (c : J → ℕ) (X Y : I → J → ℕ)
    (hX : ∀ i j, firstPaperSmall r c (dimensionAllowance (I := I) (J := J)^20) i j=true →
      X i j ≤ dimensionAllowance (I := I) (J := J)^20)
    (hY : ∀ i j, firstPaperSmall r c (dimensionAllowance (I := I) (J := J)^20) i j=true →
      Y i j ≤ dimensionAllowance (I := I) (J := J)^20) :
    firstPaperHardSum r c X Y=firstPaperWeight r c X Y := by
  apply hard_count_eq
  · intro i j hij
    simpa only [paperCapacity,hij,ite_true] using hX i j hij
  · intro i j hij
    simpa only [paperCapacity,hij,ite_true] using hY i j hij
  · exact paper_capacity_excludes_none _ X r _ _ _ dimension_le_allowance

end ContingencyTables.CompletionCounts

end OAI
