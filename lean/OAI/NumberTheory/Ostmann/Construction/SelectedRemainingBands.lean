import OAI.NumberTheory.Ostmann.Construction.DiagonalCounterpartReindexBands
import OAI.NumberTheory.Ostmann.Construction.DiagonalTransformSmall
import OAI.NumberTheory.Ostmann.Construction.SelectedRemainingBandsMetadata

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction.InitialSourceChoice
variable {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ} {E : Finset ℕ}

theorem sources_disjointMass_of_role_ne (C : InitialSourceChoice d Bs BD Bz k L E)
    (spectator : PrimeSource) (hsep : C.CrossRoleSeparation spectator) {q z : SourceSlot}
    (hq : q ∈ Template.initial (2*(Conclusion.bulkSize k L/2)) k)
    (hz : z ∈ Template.initial (2*(Conclusion.bulkSize k L/2)) k)
    (hne : q.role≠z.role) : (C.sources q.origin).DisjointMass (C.sources z.origin) := by
  rcases C.source_role_cases hq with ⟨hqr,hqs⟩ | ⟨i,hqr,hqs⟩ | ⟨a,i,hqr,hqs⟩
  · rcases C.source_role_cases hz with ⟨hzr,hzs⟩ | ⟨j,hzr,hzs⟩ | ⟨b,j,hzr,hzs⟩
    · exact (hne (hqr.trans hzr.symm)).elim
    · rw [hqs,hzs]
      exact hsep.bulk_aux (.inl j)
    · rw [hqs,hzs]
      exact hsep.bulk_aux (.inr (b,j))
  · rcases C.source_role_cases hz with ⟨hzr,hzs⟩ | ⟨j,hzr,hzs⟩ | ⟨b,j,hzr,hzs⟩
    · rw [hqs,hzs]
      exact (hsep.bulk_aux (.inl i)).symm
    · exact (hne (hqr.trans hzr.symm)).elim
    · rw [hqs,hzs]
      exact hsep.top_comp i b j
  · rcases C.source_role_cases hz with ⟨hzr,hzs⟩ | ⟨j,hzr,hzs⟩ | ⟨b,j,hzr,hzs⟩
    · rw [hqs,hzs]
      exact (hsep.bulk_aux (.inr (a,i))).symm
    · rw [hqs,hzs]
      exact (hsep.top_comp j a i).symm
    · rw [hqs,hzs]
      apply hsep.comp_comp a b _ i j
      intro he
      subst b
      exact hne (hqr.trans hzr.symm)

theorem bandsSeparated_of_initial_slots (C : InitialSourceChoice d Bs BD Bz k L E)
    (spectator : PrimeSource) (hsep : C.CrossRoleSeparation spectator)
    (T : List SourceSlot)
    (hT : ∀ q ∈ T, q ∈ Template.initial (2*(Conclusion.bulkSize k L/2)) k) :
    RemainingBandsSeparated C.sources T C.giant := by
  intro i j hne
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => exact (hne rfl).elim
    | succ j =>
      exact C.giant_sources_disjointMass spectator hsep T[j].origin
  | succ i =>
    induction j using Fin.cases with
    | zero => exact (C.giant_sources_disjointMass spectator hsep T[i].origin).symm
    | succ j =>
      apply C.sources_disjointMass_of_role_ne spectator hsep
        (hT T[i] (List.getElem_mem i.isLt)) (hT T[j] (List.getElem_mem j.isLt))
      intro he
      apply hne
      exact congrArg some he

theorem remaining_bandsSeparated (C : InitialSourceChoice d Bs BD Bz k L E)
    (spectator : PrimeSource) (hsep : C.CrossRoleSeparation spectator) (l : ℕ) :
    RemainingBandsSeparated C.sources
      (Template.remainder (l+1) (Template.current
        (Template.initial (2*(Conclusion.bulkSize k L/2)) k) l)) C.giant :=
  C.bandsSeparated_of_initial_slots spectator hsep _
    (fun _ hq => Template.mem_remainder_current_mem_seed hq)

theorem current_bandsSeparated (C : InitialSourceChoice d Bs BD Bz k L E)
    (spectator : PrimeSource) (hsep : C.CrossRoleSeparation spectator) (l : ℕ) :
    RemainingBandsSeparated C.sources
      (Template.current (Template.initial (2*(Conclusion.bulkSize k L/2)) k) l) C.giant :=
  C.bandsSeparated_of_initial_slots spectator hsep _
    (fun _ hq => Template.mem_current_mem_seed hq)

end Ostmann.Construction.InitialSourceChoice

end

end OAI
