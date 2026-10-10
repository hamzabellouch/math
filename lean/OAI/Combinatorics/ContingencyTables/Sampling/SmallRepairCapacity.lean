import OAI.Combinatorics.ContingencyTables.Sampling.SmallProfileRepair
import OAI.Combinatorics.ContingencyTables.Sampling.PhysicalContextVariance

namespace OAI

/-! # A positive physical defect repairs inside the literal small box -/

namespace ContingencyTables.SmallGraphProfiles

open scoped Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open FirstPaperPhysicalMarginal PaddedCompletions CompletionCounts

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

/-- Positive hard marginal supplies an actual full completion. Its
preserved residual bounds force each repaired small entry below U. -/
theorem repair_small_capacity (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (z : SmallProfile (firstPaperSmall r c U))
    (hz : ∀ a,z a ≤ B a.1.val.1 a.1.val.2) (s t : I×J)
    (hs : firstPaperSmall r c U s.1 s.2=true) (ht : firstPaperSmall r c U t.1 t.2=true)
    (hd : IsDefect (smallView (firstPaperSmall r c U) z false)
      (smallQ (firstPaperSmall r c U) B z) s t)
    (hf : 0 < hardMarginal (firstPaperSmall r c U) B r c L z) :
    ∀ a : Cells (firstPaperSmall r c U),
      repairMatrix (smallView (firstPaperSmall r c U) z false) s t a.val.1 a.val.2 ≤ B a.val.1 a.val.2 := by
  have hcard : 0 < Fintype.card (CompletionFibre (firstPaperSmall r c U) B r
      (fun i => r i+rowLargeCount (firstPaperSmall r c U) i*L) c
      (fun j => c j+columnLargeCount (firstPaperSmall r c U) j*L) z) := by
    have h := hf
    rw [hardMarginal_eq_fibre_card _ _ _ _ _ z hz] at h
    exact_mod_cast h
  obtain ⟨Z⟩ := Fintype.card_pos_iff.mp hcard
  have hfull := defect_fibre_views Z hs ht hd
  intro a
  have hcap := repairMatrix_small_capacity r c U hfull hs ht Z.property.1 Z.property.2.1
    a.val.1 a.val.2 a.property
  have he : repairMatrix Z.val.val.1 s t a.val.1 a.val.2=
      repairMatrix (smallView (firstPaperSmall r c U) z false) s t a.val.1 a.val.2 := by
    apply repairMatrix_pointwise
    have hx := (Z.property.2.2.1 a.val.1 a.val.2 a.property).1
    simpa only [smallView,a.property,dite_eq_left] using hx
  rw [he] at hcap
  rw [hB _ _ a.property]
  exact Nat.le_of_lt hcap

end ContingencyTables.SmallGraphProfiles

end OAI
