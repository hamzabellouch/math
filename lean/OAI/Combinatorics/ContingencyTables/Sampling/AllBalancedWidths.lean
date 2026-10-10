import OAI.Combinatorics.ContingencyTables.Sampling.SmallBalancedMarginal
import OAI.Combinatorics.ContingencyTables.Transport.EqualityReindex

namespace OAI

/-! # The actual balanced finite family allows every small-cell capacity

The proved zero/one boundary cases complete the finite balanced
elimination theorem. The physical equality-softened tree marginal can
therefore eliminate the original small cells directly.
-/

namespace ContingencyTables.BalancedBox

open scoped BigOperators Classical
open IntegerMarginal

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem marginal_removal_slice_all (F : ((I⊕Bool) → ℕ) → ℝ)
    (m : I → ℕ) (R M : ℕ)
    (hpos : PositiveSlice F (profile m M M) (R+M))
    (hsig : RemovalSlice F (profile m M M) (R+M)) :
    RemovalSlice (marginal F M) m R := by
  rcases M with _|M
  · exact marginal_zero_removal_slice F m R (by simpa only [add_zero] using hsig)
  rcases M with _|M
  · exact marginal_one_removal_slice F m R hpos hsig
  · exact marginal_removal_slice F m R _ (by omega) hpos hsig

end ContingencyTables.BalancedBox

namespace ContingencyTables.BalancedFamily

open scoped BigOperators Classical
open IntegerMarginal BalancedBox

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Every original small-cell width, including zero and one, may be
eliminated on its precise box-valid total slice. -/
theorem eliminate_slices_all (Ms : List ℕ) (m : I → ℕ) (R : ℕ)
    (F : (Coordinates I Ms → ℕ) → ℝ)
    (hpos : PositiveSlice F (bounds m Ms) (R+Ms.sum))
    (hsig : RemovalSlice F (bounds m Ms) (R+Ms.sum)) :
    PositiveSlice (eliminate Ms F) m R ∧ RemovalSlice (eliminate Ms F) m R := by
  induction Ms with
  | nil => simpa only [List.sum_nil,add_zero,eliminate,bounds] using And.intro hpos hsig
  | cons M Ms ih =>
    have htotal : R+(M::Ms).sum=(R+Ms.sum)+M := by simp only [List.sum_cons]; omega
    rw [htotal] at hpos hsig
    exact ih (marginal F M)
      (marginal_positive_slice F (bounds m Ms) (R+Ms.sum) M hpos)
      (marginal_removal_slice_all F (bounds m Ms) (R+Ms.sum) M hpos hsig)

end ContingencyTables.BalancedFamily

namespace ContingencyTables.EqualityReindex

open scoped BigOperators Classical
open EqualitySoftening BalancedFamily BalancedBox

variable {S D G : Type*} [Fintype S] [DecidableEq S] [Fintype D] [Fintype G]

omit [DecidableEq S] in
lemma softenedWeight_reindex (Ms : List ℕ) (e : Coordinates S Ms ≃ D)
    (line : D → G) (root : G → Bool) (rate offset slope : G → ℝ)
    (urate ell uslope cap : D → ℝ) (L : ℝ) (z : Coordinates S Ms → ℕ) :
    softenedWeight (line ∘ e) root rate offset slope (urate ∘ e) (ell ∘ e)
      (uslope ∘ e) (cap ∘ e) L z=
      softenedWeight line root rate offset slope urate ell uslope cap L (z ∘ e.symm) := by
  unfold softenedWeight
  exact productWeight_reindex e line (lineFactor root rate offset slope L)
    (unaryFactor urate ell uslope cap) z

/-- The literal physical positive factor family can retain one tree
pair while summing all other original pairs, at every capacity. -/
theorem physical_softened_slices_all (Ms : List ℕ) (m : S → ℕ) (R : ℕ)
    (e : Coordinates S Ms ≃ D) (line : D → G) (root : G → Bool)
    (rate offset slope : G → ℝ) (urate ell uslope cap : D → ℝ) (L : ℝ)
    (hrate : ∀ g,0 ≤ rate g) (hu : ∀ d,0 ≤ urate d) (hL : 0 ≤ L) :
    PositiveSlice (eliminate Ms (fun z =>
      softenedWeight line root rate offset slope urate ell uslope cap L (z ∘ e.symm))) m R ∧
    RemovalSlice (eliminate Ms (fun z =>
      softenedWeight line root rate offset slope urate ell uslope cap L (z ∘ e.symm))) m R := by
  have heq : (fun z => softenedWeight line root rate offset slope urate ell uslope cap L
      (z ∘ e.symm))=softenedWeight (line ∘ e) root rate offset slope
      (urate ∘ e) (ell ∘ e) (uslope ∘ e) (cap ∘ e) L := by
    funext z
    exact (softenedWeight_reindex Ms e line root rate offset slope urate ell uslope cap L z).symm
  rw [heq]
  apply eliminate_slices_all Ms m R
  · intro z _ _
    exact softenedWeight_positive (line ∘ e) root rate offset slope
      (urate ∘ e) (ell ∘ e) (uslope ∘ e) (cap ∘ e) L z
  · intro z _ _
    convert softenedWeight_removal (line ∘ e) root rate offset slope
      (urate ∘ e) (ell ∘ e) (uslope ∘ e) (cap ∘ e) L hrate (fun i => hu (e i)) hL z using 1
    congr 2 <;> exact Subsingleton.elim _ _

end ContingencyTables.EqualityReindex

end OAI
