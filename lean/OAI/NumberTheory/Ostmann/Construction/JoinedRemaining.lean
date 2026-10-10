import OAI.NumberTheory.Ostmann.Construction.AssignmentSlots
import OAI.NumberTheory.Ostmann.Construction.RemainingRows

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction

theorem assignment_append_slots_cmean (sources : SourceFamily) (T U : List SourceSlot)
    (F : List SmallSlot→ℂ) :
    (assignmentPrior sources (T++U)).cmean (fun x => F (assignedSlots sources (T++U) x))=
      (assignmentPrior sources T).cmean (fun x => (assignmentPrior sources U).cmean (fun y =>
        F (assignedSlots sources T x++assignedSlots sources U y))) := by
  have h := assignmentAppend_cmean sources T U
    (fun xy => F (assignedSlots sources T xy.1++assignedSlots sources U xy.2))
  simp_rw [←assignedSlots_append] at h
  exact h

def joinedRemainingState (sources : SourceFamily) (T : List SourceSlot) (giant : PrimeSource)
    (x y : RemainingSample sources T giant) (s : ℤ) : State :=
  ⟨s,x.1.val,y.1.val,assignedSlots sources T x.2++assignedSlots sources T y.2⟩

theorem outerPrior_join (sources : SourceFamily) (T : List SourceSlot) (giant : PrimeSource)
    (s : ℤ) (F : State→ℂ) :
    (outerPrior sources (T++T) giant).cmean (fun x => F (outerState sources (T++T) giant x s))=
      (remainingPrior sources T giant).cmean (fun x =>
        (remainingPrior sources T giant).cmean (fun y => F (joinedRemainingState sources T giant x y s))) := by
  unfold outerPrior remainingPrior
  simp_rw [FinitePrior.pair_cmean]
  apply congrArg (FinitePrior.cmean giant.law)
  funext p
  change giant.law.cmean (fun q => (assignmentPrior sources (T++T)).cmean
      (fun a => F ⟨s,p.val,q.val,assignedSlots sources (T++T) a⟩)) = _
  calc
    _ = giant.law.cmean (fun q => (assignmentPrior sources T).cmean (fun x =>
        (assignmentPrior sources T).cmean (fun y =>
          F ⟨s,p.val,q.val,assignedSlots sources T x++assignedSlots sources T y⟩))) := by
      apply congrArg (FinitePrior.cmean giant.law)
      funext q
      exact assignment_append_slots_cmean sources T T (fun slots => F ⟨s,p.val,q.val,slots⟩)
    _ = _ := FinitePrior.cmean_comm giant.law (assignmentPrior sources T)
      (fun q x => (assignmentPrior sources T).cmean (fun y =>
        F ⟨s,p.val,q.val,assignedSlots sources T x++assignedSlots sources T y⟩))

namespace FinitePrior

theorem cmean_congr_support {α : Type*} [Fintype α] (μ : FinitePrior α)
    (f g : α→ℂ) (h : ∀x,μ.mass x≠0→f x=g x) : μ.cmean f=μ.cmean g := by
  unfold cmean
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hm : μ.mass x=0
  · simp only [hm,Complex.ofReal_zero,zero_mul]
  · rw [h x hm]
end FinitePrior

theorem actualAmplitude_joined (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ)
    (giant spectator : PrimeSource) (m : ℕ) (X G : ℝ)
    (g gt : (p:ℕ)→ZMod p→ℂ) (bins : List ℕ→State→ℝ) (l : ℕ) :
    actualAmplitude sources seed V giant spectator m X G g gt bins (l+1)=
      (spectatorPrior spectator m).cmean (fun ds =>
        (remainingPrior sources (Template.remainder (l+1) (Template.current seed l)) giant).cmean (fun x =>
          (remainingPrior sources (Template.remainder (l+1) (Template.current seed l)) giant).cmean (fun y =>
            ∑s:AllowedFrequency V (l+1),
              let a := joinedRemainingState sources (Template.remainder (l+1) (Template.current seed l)) giant x y s.val
              regularTransform g gt (spectatorList spectator ds) a *
                actualCoefficient sources seed V X G g bins (spectatorList spectator ds) (l+1) a))) := by
  unfold actualAmplitude
  apply congrArg (FinitePrior.cmean (spectatorPrior spectator m))
  funext ds
  change (outerPrior sources ((Template.remainder (l+1) (Template.current seed l))++
      (Template.remainder (l+1) (Template.current seed l))) giant).cmean _ = _
  have he := outerPrior_join sources (Template.remainder (l+1) (Template.current seed l)) giant 0
    (fun a => ∑s:AllowedFrequency V (l+1),
      let b := {a with frequency:=s.val}
      regularTransform g gt (spectatorList spectator ds) b *
        actualCoefficient sources seed V X G g bins (spectatorList spectator ds) (l+1) b)
  exact he

end Ostmann.Construction

end

end OAI
