import OAI.Probability.DilutedSpin.PhysicalMultileafMoments
import OAI.Probability.DilutedSpin.ShiftedFrameGeometry
import OAI.Probability.DilutedSpin.VertexContinuity

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {n m : ℕ}
@[simp] lemma branchingCount_heightCast (h : n=m) (S : PrescribedTree n) (P : ℕ → Prop) :
    branchingCount (heightCast h S) P=branchingCount S P := by cases h; rfl

lemma branchRegular_heightCast (h : n=m) (S : PrescribedTree n) (d L : ℕ) (η : ℝ) :
    BranchRegular (heightCast h S) (grid m d L) η ↔ BranchRegular S (grid n d L) η := by
  cases h; rfl

lemma branchingCount_splitFrame_bottom (S : PrescribedTree n) (r d : ℕ) (P : ℕ → Prop) :
    branchingCount (splitFrame (bottomUnary S) r d) P =
      branchingCount (stem (doubled (bottomUnary (stem S r))) d) P := by
  simp only [splitFrame,branchingCount_stem,doubled,branchingCount,branchingCount_bottom]

end DilutedSpinGlass.PrescribedTree

namespace DilutedSpinGlass.ReducedTopology
open PrescribedTree
open scoped BigOperators
variable {α : Type} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
/-- The scheduled old frame has no charged internal branching vertex.
No regularity of a union of old and target trees is postulated. -/
theorem scheduled_frame_old_count (H r d : ℕ) (k : ℕ+) (a : α)
    (C : Fin k → ReducedTopology) (e : (j : Fin k) → (C j).Vertex → {j : α // j≠a})
    (Q : α → Fin (H+1+1+r+1+d))
    (had : ∀ j, Admissible (C j) (fun v => (Q (e j v)).val) (r+1+d+1) (r+1+d+1+H))
    (hno : NoAdjacentBranchDepths
      (stem (PrescribedTree.node k (fun j => realize H (r+1+d+1) (C j) (fun v => (Q (e j v)).val))) r)) :
    let Base := PrescribedTree.node k (fun j => realize H (r+1+d+1) (C j) (fun v => (Q (e j v)).val))
    let Old := PrescribedTree.node k (fun j => realize (H+1) (r+1+d+1) (C j) (fun v => (Q (e j v)).val))
    branchingCount (splitFrame Old r d) (· ∈ shiftedPrefixDepths (stem Base r) d)=0 := by
  dsimp only
  have he : (PrescribedTree.node k (fun j => realize (H+1) (r+1+d+1) (C j)
      (fun v => (Q (e j v)).val))) =
      bottomUnary (PrescribedTree.node k (fun j => realize H (r+1+d+1) (C j)
        (fun v => (Q (e j v)).val))) := by
    change PrescribedTree.node k _=PrescribedTree.node k _
    congr 1
    funext j
    exact realize_bottom H (r+1+d+1) (C j) _ (had j)
  rw [he,branchingCount_splitFrame_bottom]
  exact shifted_prefix_old_count _ d hno

omit [Fintype α] [DecidableEq α] in
/-- The delayed scheduled target contains exactly two occurrences of each
branching vertex of the base, even if both copies have equal assigned depths. -/
theorem scheduled_frame_target_count (H r d : ℕ) (k : ℕ+) (a : α)
    (C : Fin k → ReducedTopology) (e : (j : Fin k) → (C j).Vertex → {j : α // j≠a})
    (Q : α → Fin (H+1+1+r+1+d)) :
    let Base := PrescribedTree.node k (fun j => realize H (r+1+d+1) (C j) (fun v => (Q (e j v)).val))
    let New := PrescribedTree.node k (fun j => realize H (r+1+1+d+1) (C j) (fun v => (Q (e j v)).val+1))
    let Target := heightCast (shiftedFrameHeight H r d) (splitFrame New (r+1) d)
    branchingCount Target (· ∈ shiftedPrefixDepths (stem Base r) d)=
      2*branchingCount Base (fun _ => True) := by
  dsimp only
  rw [branchingCount_heightCast]
  have he : (PrescribedTree.node k (fun j => realize H (r+1+1+d+1) (C j)
      (fun v => (Q (e j v)).val+1))) =
      PrescribedTree.node k (fun j => realize H (r+1+d+1) (C j) (fun v => (Q (e j v)).val)) := by
    congr 1
    funext j
    rw [show r+1+1+d+1=(r+1+d+1)+1 by omega,realize_translate]
  rw [he]
  change branchingCount (stem (doubled (unary (stem _ r))) d) _=_
  rw [shifted_prefix_target_count,branchingCount_stem]

omit [Fintype α] [DecidableEq α] in
/-- All target branches except the protected separation vertex are charged. -/
theorem scheduled_frame_target_total (H r d : ℕ) (k : ℕ+) (a : α)
    (C : Fin k → ReducedTopology) (e : (j : Fin k) → (C j).Vertex → {j : α // j≠a})
    (Q : α → Fin (H+1+1+r+1+d)) :
    let Base := PrescribedTree.node k (fun j => realize H (r+1+d+1) (C j) (fun v => (Q (e j v)).val))
    let New := PrescribedTree.node k (fun j => realize H (r+1+1+d+1) (C j) (fun v => (Q (e j v)).val+1))
    let Target := heightCast (shiftedFrameHeight H r d) (splitFrame New (r+1) d)
    branchingCount Target (fun _ => True)=
      branchingCount Target (· ∈ shiftedPrefixDepths (stem Base r) d)+1 := by
  dsimp only
  simp only [branchingCount_heightCast]
  have he : (PrescribedTree.node k (fun j => realize H (r+1+1+d+1) (C j)
      (fun v => (Q (e j v)).val+1))) =
      PrescribedTree.node k (fun j => realize H (r+1+d+1) (C j) (fun v => (Q (e j v)).val)) := by
    congr 1
    funext j
    rw [show r+1+1+d+1=(r+1+d+1)+1 by omega,realize_translate]
  rw [he]
  change branchingCount (stem (doubled (unary (stem _ r))) d) _=_
  exact shifted_prefix_total_count _ d

omit [Fintype α] [DecidableEq α] in
/-- Higher-degree target factors are uniformly interior at every regular
first split. No premise is imposed on an overlay of the two shapes. -/
theorem scheduled_frame_target_regular (H r d : ℕ) (k : ℕ+) (a : α)
    (C : Fin k → ReducedTopology) (e : (j : Fin k) → (C j).Vertex → {j : α // j≠a})
    (Q : α → Fin (H+1+1+r+1+d)) (η : ℝ)
    (heval : η≤((d+r+2:ℕ):ℝ)/((H+1+1+r+1+d:ℕ):ℝ)) :
    let New := PrescribedTree.node k (fun j => realize H (r+1+1+d+1) (C j) (fun v => (Q (e j v)).val+1))
    let Target := heightCast (shiftedFrameHeight H r d) (splitFrame New (r+1) d)
    BranchRegular Target (grid (H+1+1+r+1+d) 0 (H+1+1+r+1+d)) η := by
  dsimp only
  rw [branchRegular_heightCast]
  change BranchRegular (stem (doubled (unary (stem _ r))) d) _ _
  exact branchRegular_shifted_frame _ r d _ η heval

end DilutedSpinGlass.ReducedTopology
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

/-- The literal tail of the universal dictionary's reversed insertion list. -/
def canonicalMatrixTail (t : ℕ) : List (Option (Fin (t+1))) :=
  (List.ofFn (fun j : Fin t => some j.castSucc)).reverse

lemma canonicalMatrixHistory (t : ℕ) :
    (List.ofFn (fun j : Fin (t+1) => (some j : Option (Fin (t+1))))).reverse =
      some (Fin.last t) :: canonicalMatrixTail t := by
  rw [List.ofFn_succ_last, List.reverse_append]
  rfl

lemma canonicalMatrixTail_nodup (t : ℕ) : (canonicalMatrixTail t).Nodup := by
  apply List.nodup_reverse.mpr
  exact List.nodup_ofFn.mpr (fun i j h => Fin.castSucc_injective t (Option.some_injective _ h))

lemma canonicalMatrixTail_not_mem (t : ℕ) (x : Option (Fin (t+1)))
    (hx : x ∈ canonicalMatrixTail t) :
    x ∉ insert (some (Fin.last t)) ({none} : Finset (Option (Fin (t+1)))) := by
  simp only [canonicalMatrixTail, List.mem_reverse, List.mem_ofFn] at hx
  obtain ⟨j, rfl⟩ := hx
  simp only [Finset.mem_insert, Finset.mem_singleton, Option.some.injEq, Option.some_ne_none,
    or_false]
  exact Fin.castSucc_ne_last j

lemma canonicalMatrixTail_full (t : ℕ) :
    insert (some (Fin.last t)) ({none} : Finset (Option (Fin (t+1)))) ∪
      (canonicalMatrixTail t).toFinset = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro x
  cases x with
  | none => simp
  | some j =>
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp
    · apply Finset.mem_union.mpr (Or.inr _)
      simp only [List.mem_toFinset, canonicalMatrixTail, List.mem_reverse, List.mem_ofFn]
      exact ⟨i,rfl⟩

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
