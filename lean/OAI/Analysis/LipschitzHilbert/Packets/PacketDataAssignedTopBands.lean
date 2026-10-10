import OAI.Analysis.LipschitzHilbert.Packets.PacketDataAssignedTopAlternate
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataAssignedPhysical

namespace OAI

/-! Assigned top bands retain the actual top mask and physical packet. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)

theorem assignedTopFamily_physicalMaskedValue (top : τ) (t : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ) (z : ℝ×ℝ)
    (q : (P.assignedTopFamily packets assigned top).PacketIndex) :
    (P.assignedTopFamily packets assigned top).physicalMaskedValue
      (P.assignedTopAlternate packets assigned alt top)
      (P.assignedTopAlternate_bound packets assigned alt hAlt top) t
      (fun j l => b j l.val.2) v f (fun j l u => T j l.val.2 u.val) L A z q =
      P.physicalMaskedValue alt hAlt t b v f T L A z
        ⟨q.1,⟨q.2.1.val.2,q.2.2.val⟩⟩ := rfl

theorem assignedTopFamily_physicalMaskedBand (top : τ) (t : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ) (z : ℝ×ℝ) (j : Fin N) :
    (P.assignedTopFamily packets assigned top).physicalMaskedBand
      (P.assignedTopAlternate packets assigned alt top)
      (P.assignedTopAlternate_bound packets assigned alt hAlt top) t
      (fun j l => b j l.val.2) v f (fun j l u => T j l.val.2 u.val)
      L A (z.2-t*z.1) j z.1 =
      P.assignedPhysicalBands alt hAlt t b v f T L A packets assigned z (top,j) := by
  let Q := P.assignedTopFamily packets assigned top
  have hpoint : (z.1,z.2-t*z.1+t*z.1) = z := by
    apply Prod.ext
    · rfl
    · dsimp
      ring
  have hband := Q.physicalMaskedValue_length_sum
    (P.assignedTopAlternate packets assigned alt top)
    (P.assignedTopAlternate_bound packets assigned alt hAlt top) t
    (fun j l => b j l.val.2) v f (fun j l u => T j l.val.2 u.val) L A
    (z.2-t*z.1) z.1 j
  rw [hpoint] at hband
  apply hband.symm.trans
  have hs := P.sum_assignedTopPackets_filter packets assigned top
    (P.physicalMaskedValue alt hAlt t b v f T L A z) (fun q => q.1 = j)
  calc
    _ = ∑ q ∈ Finset.univ.filter (fun q : Q.PacketIndex => q.1 = j),
        P.physicalMaskedValue alt hAlt t b v f T L A z
          ⟨q.1,⟨q.2.1.val.2,q.2.2.val⟩⟩ := by
      apply Finset.sum_congr rfl
      intro q _
      exact P.assignedTopFamily_physicalMaskedValue packets assigned alt hAlt top t b v f T L A z q
    _ = ∑ q ∈ (packets.filter (fun q => assigned q = top)).filter (fun q => q.1 = j),
        P.physicalMaskedValue alt hAlt t b v f T L A z q := by
      convert hs using 1 <;> apply Finset.sum_congr
      · ext q
        simp
      · intro q _
        rfl
      · ext q
        simp
      · intro q _
        rfl
    _ = _ := by
      rw [P.assignedPhysicalBands_eq alt hAlt t b v f T L A packets assigned z (top,j)]
      apply Finset.sum_congr
      · ext q
        simp only [Finset.mem_filter,Prod.mk.injEq,and_assoc]
      · intro q _
        rfl

/-- The mask on an assigned family is its single assigned top mask. -/
theorem assignedTopFamily_single_mask (top : τ) (T : τ → SlopeBox) :
    (fun j (l : (P.assignedTopFamily packets assigned top).labels j)
      (u : P.AssignedTopItem packets assigned j l) =>
        T (assigned ⟨j,⟨l.val.2,u.val⟩⟩)) = fun _ _ _ => T top := by
  funext j l u
  have ht : l.val.1 = top := Finset.mem_singleton.mp (Finset.mem_product.mp l.property).1
  rw [u.property.2,ht]

theorem assignedTopFamily_topMaskBand (top : τ) (t : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ) (T : τ → SlopeBox)
    (L A : ℝ) (z : ℝ×ℝ) (j : Fin N) :
    (P.assignedTopFamily packets assigned top).physicalMaskedBand
      (P.assignedTopAlternate packets assigned alt top)
      (P.assignedTopAlternate_bound packets assigned alt hAlt top) t
      (fun j l => b j l.val.2) v f (fun _ _ _ => T top) L A (z.2-t*z.1) j z.1 =
      P.assignedPhysicalBands alt hAlt t b v f
        (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A packets assigned z (top,j) := by
  have h := P.assignedTopFamily_physicalMaskedBand packets assigned alt hAlt top t b v f
    (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z j
  rw [P.assignedTopFamily_single_mask packets assigned top T] at h
  exact h

end LipschitzHilbert.PacketLatticeData

end

end OAI
