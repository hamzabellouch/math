import OAI.Combinatorics.ContingencyTables.Transport.BalancedBox
import OAI.Combinatorics.ContingencyTables.Transport.ProductIntegerSignature

namespace OAI

/-!
# The actual finite-box fixed-total weight

Truncating the positive product outside its box and required total leaves
every valid two-removal matrix entry unchanged at a box-valid display two
above that total. The balancing development therefore applies to the
paper's literal zero-extended weight.
-/

namespace ContingencyTables.IntegerBoxTruncation

open scoped BigOperators Classical Matrix
open CommonBasesFPRAS FactorialSignatures ProductIntegerSignature BalancedBox

variable {I : Type*} [Fintype I]

noncomputable def truncate (f : (I → ℕ) → ℝ) (m : I → ℕ) (R : ℕ) (z : I → ℕ) : ℝ :=
  if InBox m z ∧ (∑ i, z i)=R then f z else 0

omit [Fintype I] in
lemma removal_inBox (m z : I → ℕ) (hz : InBox m z) (i j : I) : InBox m (removeTwo z i j) := by
  intro k
  apply le_trans _ (hz k)
  unfold removeTwo removeOne
  omega

lemma removal_total (z : I → ℕ) (i j : I) (hv : ValidPair z i j) :
    (∑ k, removeTwo z i j k)+2=∑ k, z k := by
  have h := lineTotal_removeTwo (fun _ : I => ()) z i j hv ()
  simp only [lineTotal,ite_true] at h
  omega

/-- Exact equality of the actual truncated and product integer matrices. -/
theorem removal_truncate_eq (f : (I → ℕ) → ℝ) (m z : I → ℕ) (R : ℕ)
    (hz : InBox m z) (ht : (∑ i, z i)=R+2) :
    integerRemovalMatrix (truncate f m R) z = integerRemovalMatrix f z := by
  ext i j
  unfold integerRemovalMatrix
  split_ifs with hv
  · have hb := removal_inBox m z hz i j
    have htotal := removal_total z i j hv
    have he : (∑ k, removeTwo z i j k)=R := by omega
    simp [truncate,hb,he]
  · rfl

/-- Positivity on the actual slice is unchanged by literal zero extension. -/
theorem truncate_positive_slice (f : (I → ℕ) → ℝ) (m : I → ℕ) (R : ℕ)
    (hpos : PositiveSlice f m R) : PositiveSlice (truncate f m R) m R := by
  intro z hz ht
  have hb : InBox m z ∧ (∑ i, z i)=R := ⟨hz,ht⟩
  simpa only [truncate,ite_eq_left hb] using hpos z hz ht

/-- The actual integer signature is unchanged by the box/total indicator. -/
theorem truncate_removal_slice (f : (I → ℕ) → ℝ) (m : I → ℕ) (R : ℕ)
    (hsig : RemovalSlice f m R) : RemovalSlice (truncate f m R) m R := by
  intro z hz ht
  rw [removal_truncate_eq f m z R hz ht]
  exact hsig z hz ht

end ContingencyTables.IntegerBoxTruncation

end OAI
