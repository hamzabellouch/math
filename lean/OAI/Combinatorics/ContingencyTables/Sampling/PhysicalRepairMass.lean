import OAI.Combinatorics.ContingencyTables.Sampling.SmallRepairCapacity

namespace OAI

/-! # Literal completion-retaining repair dominates the physical weight -/

namespace ContingencyTables.SmallGraphProfiles

open scoped Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open FirstPaperPhysicalMarginal PaddedCompletions CompletionCounts

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable def completionJointDefect (small : I → J → Bool) (B : I → J → ℕ)
    (r rbar : I → ℕ) (c cbar : J → ℕ) (z : SmallProfile small) (s t : I×J)
    (hs : small s.1 s.2=true) (ht : small t.1 t.2=true)
    (hd : IsDefect (smallView small z false) (smallQ small B z) s t)
    (Z : CompletionFibre small B r rbar c cbar z) : JointDefect small r c rbar cbar s t :=
  ⟨Z.val,defect_fibre_views Z hs ht hd,Z.property.1,Z.property.2.1⟩

lemma jointRepair_small_entry (small : I → J → Bool) (B : I → J → ℕ)
    (r rbar : I → ℕ) (c cbar : J → ℕ) (z : SmallProfile small) (s t : I×J)
    (hs : small s.1 s.2=true) (ht : small t.1 t.2=true)
    (hd : IsDefect (smallView small z false) (smallQ small B z) s t)
    (Z : CompletionFibre small B r rbar c cbar z) (i : I) (j : J) (hij : small i j=true) :
    (jointRepair hs ht (completionJointDefect small B r rbar c cbar z s t hs ht hd Z)).val.val i j=
      repairMatrix (smallView small z false) s t i j := by
  change repairMatrix Z.val.val.1 s t i j=repairMatrix (smallView small z false) s t i j
  apply repairMatrix_pointwise
  have hx := (Z.property.2.2.1 i j hij).1
  simpa only [smallView,hij,dite_eq_left] using hx

noncomputable def repairedCompletion (small : I → J → Bool) (B : I → J → ℕ)
    (r rbar : I → ℕ) (c cbar : J → ℕ) (z : SmallProfile small) (s t : I×J)
    (hs : small s.1 s.2=true) (ht : small t.1 t.2=true)
    (hd : IsDefect (smallView small z false) (smallQ small B z) s t)
    (hsmall : ∀ a : Cells small,repairMatrix (smallView small z false) s t a.val.1 a.val.2 ≤ B a.val.1 a.val.2)
    (hcap : ∀ T : ResidualTables small r c rbar cbar,∀ i j,T.val.val i j ≤ B i j)
    (Z : CompletionFibre small B r rbar c cbar z) :
    CompletionFibre small B r rbar c cbar (repairedProfile small B z s t) := by
  let T := jointRepair hs ht (completionJointDefect small B r rbar c cbar z s t hs ht hd Z)
  refine ⟨⟨(T.val.val,T.val.val),T.val.property.1,T.val.property.2⟩,T.property.1,T.property.2,?_,?_,?_⟩
  · intro i j hij
    have he := jointRepair_small_entry small B r rbar c cbar z s t hs ht hd Z i j hij
    change T.val.val i j=repairMatrix (smallView small z false) s t i j at he
    constructor
    · exact he
    · change T.val.val i j=B i j-(B i j-repairMatrix (smallView small z false) s t i j)
      rw [he]
      exact (Nat.sub_sub_self (hsmall ⟨(i,j),hij⟩)).symm
  · intro _ _ _
    rfl
  · intro i j _
    exact hcap T i j

lemma repairedCompletion_injective (small : I → J → Bool) (B : I → J → ℕ)
    (r rbar : I → ℕ) (c cbar : J → ℕ) (z : SmallProfile small) (s t : I×J)
    (hs : small s.1 s.2=true) (ht : small t.1 t.2=true)
    (hd : IsDefect (smallView small z false) (smallQ small B z) s t)
    (hsmall : ∀ a : Cells small,repairMatrix (smallView small z false) s t a.val.1 a.val.2 ≤ B a.val.1 a.val.2)
    (hcap : ∀ T : ResidualTables small r c rbar cbar,∀ i j,T.val.val i j ≤ B i j) :
    Function.Injective (repairedCompletion small B r rbar c cbar z s t hs ht hd hsmall hcap) := by
  intro X Y he
  have htables : jointRepair hs ht (completionJointDefect small B r rbar c cbar z s t hs ht hd X)=
      jointRepair hs ht (completionJointDefect small B r rbar c cbar z s t hs ht hd Y) := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun V => V.val.val.1) he
  have hj := jointRepair_injective hs ht htables
  apply Subtype.ext
  exact congrArg (fun V : JointDefect small r c rbar cbar s t => V.val) hj

/-- The repair is the manuscript's actual profile map, and the weight
inequality counts all completions through its explicit injective map. -/
theorem physical_repair_weight_le (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (z : SmallProfile (firstPaperSmall r c U))
    (hz : ∀ a,z a ≤ B a.1.val.1 a.1.val.2) (s t : I×J)
    (hs : firstPaperSmall r c U s.1 s.2=true) (ht : firstPaperSmall r c U t.1 t.2=true)
    (hd : IsDefect (smallView (firstPaperSmall r c U) z false)
      (smallQ (firstPaperSmall r c U) B z) s t)
    (hcap : ∀ T : ResidualTables (firstPaperSmall r c U) r c
      (fun i => r i+rowLargeCount (firstPaperSmall r c U) i*L)
      (fun j => c j+columnLargeCount (firstPaperSmall r c U) j*L),∀ i j,T.val.val i j ≤ B i j)
    (hf : 0 < hardMarginal (firstPaperSmall r c U) B r c L z) :
    hardMarginal (firstPaperSmall r c U) B r c L z ≤
      hardMarginal (firstPaperSmall r c U) B r c L (repairedProfile (firstPaperSmall r c U) B z s t) := by
  have hsmall := repair_small_capacity r c U L B hB z hz s t hs ht hd hf
  rw [hardMarginal_eq_fibre_card _ _ _ _ _ z hz,
    hardMarginal_eq_fibre_card _ _ _ _ _ _ (repairedProfile_bounded _ _ _ _ _ hsmall)]
  exact_mod_cast Fintype.card_le_of_injective
    (repairedCompletion _ B r _ c _ z s t hs ht hd hsmall hcap)
    (repairedCompletion_injective _ B r _ c _ z s t hs ht hd hsmall hcap)

end ContingencyTables.SmallGraphProfiles

end OAI
