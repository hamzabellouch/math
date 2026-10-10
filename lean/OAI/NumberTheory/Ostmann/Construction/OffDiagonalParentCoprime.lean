import OAI.NumberTheory.Ostmann.Construction.HistoryGiantGuard
import OAI.NumberTheory.Ostmann.Construction.JoinedFrame
import OAI.NumberTheory.Ostmann.Construction.OffDiagonalCoprime
import OAI.NumberTheory.Ostmann.Construction.RemainingSupport

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction

theorem remaining_half_pairwise (a : State) (u hp : List SmallSlot) (outside : List ℕ)
    (hperm : a.small.Perm (u ++ hp)) (hc : a.Coprime outside) :
    ((a.giantMinus :: hp.map SmallSlot.value) ++ outside).Pairwise Nat.Coprime := by
  have he : a.values.Perm ((a.giantPlus :: u.map SmallSlot.value) ++
      (a.giantMinus :: hp.map SmallSlot.value)) := by
    have h₁ := List.Perm.cons a.giantPlus (List.Perm.cons a.giantMinus (hperm.map SmallSlot.value))
    simp only [List.map_append] at h₁
    exact h₁.trans (List.Perm.cons _ List.perm_middle.symm)
  have hh := ((he.append_right outside).pairwise_iff Nat.Coprime.symm).mp hc
  rw [List.append_assoc] at hh
  exact (List.pairwise_append.mp hh).2.1

theorem joined_pairwise_of_halves (qp qm : ℕ) (hp hm : List SmallSlot) (outside : List ℕ)
    (hP : ((qp :: hp.map SmallSlot.value) ++ outside).Pairwise Nat.Coprime)
    (hM : ((qm :: hm.map SmallSlot.value) ++ outside).Pairwise Nat.Coprime)
    (hcross : (halfProduct qp hp).Coprime (halfProduct qm hm)) :
    ((qp :: qm :: (hp ++ hm).map SmallSlot.value) ++ outside).Pairwise Nat.Coprime := by
  let A := qp :: hp.map SmallSlot.value
  let B := qm :: hm.map SmallSlot.value
  have hp' := List.pairwise_append.mp hP
  have hm' := List.pairwise_append.mp hM
  have hAB : (A ++ B).Pairwise Nat.Coprime := by
    apply List.pairwise_append.mpr
    refine ⟨hp'.1,hm'.1,?_⟩
    intro a ha b hb
    exact (hcross.of_dvd_left (List.dvd_prod ha)).of_dvd_right (List.dvd_prod hb)
  have hABO : ((A ++ B) ++ outside).Pairwise Nat.Coprime := by
    apply List.pairwise_append.mpr
    refine ⟨hAB,hp'.2.1,?_⟩
    intro a ha b hb
    rcases List.mem_append.mp ha with ha | ha
    · exact hp'.2.2 a ha b hb
    · exact hm'.2.2 a ha b hb
  have he : (qp :: qm :: (hp ++ hm).map SmallSlot.value).Perm (A ++ B) := by
    simp only [List.map_append]
    exact List.Perm.cons _ List.perm_middle.symm
  exact ((he.append_right outside).pairwise_iff Nat.Coprime.symm).mpr hABO

theorem remaining_assigned_templateAt (sources : SourceFamily) (seed : List SourceSlot)
    (hseed : ∀ q ∈ seed, ∀ j, q.role = .compensation j → 0 < j) (l : ℕ)
    (x : SourceAssignment sources (Template.remainder (l+1) (Template.current seed l))) :
    ∀ q ∈ assignedSlots sources (Template.remainder (l+1) (Template.current seed l)) x,
      ∀ j, q.role = .compensation j → l+1 < j := by
  intro q hq j hrole
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
  have hi : (Template.remainder (l+1) (Template.current seed l))[i] ∈
      Template.current seed (l+1) :=
    List.mem_append_left _ (List.getElem_mem i.isLt)
  exact Template.current_types_gt seed hseed (l+1) _ hi j hrole

end Ostmann.Construction

end

end OAI
