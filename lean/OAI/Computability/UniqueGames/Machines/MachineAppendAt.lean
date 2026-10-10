import OAI.Computability.UniqueGames.Machines.MachineCompositionLemmas
import OAI.Computability.UniqueGames.Reduction.MachineTransfer

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Complexity.MachineAppendAt

open Turing

variable {K Λ σ β : Type} [DecidableEq K]

abbrev Alphabet (β : Type) (_ : K) := β

def appendTapes (source destination : K) (base : K → List β) : K → List β :=
  Reduction.MachineTransfer.tapesAt source destination base []
    (base destination ++ base source)

@[simp] theorem appendTapes_source (source destination : K)
    (distinct : source ≠ destination) (base : K → List β) :
    appendTapes source destination base source = [] := by
  simp [appendTapes, distinct]

@[simp] theorem appendTapes_destination (source destination : K) (base : K → List β) :
    appendTapes source destination base destination = base destination ++ base source := by
  simp [appendTapes]

theorem appendTapes_other (source destination k : K)
    (notSource : k ≠ source) (notDestination : k ≠ destination) (base : K → List β) :
    appendTapes source destination base k = base k := by
  simp [appendTapes, Reduction.MachineTransfer.tapesAt, notSource, notDestination]

theorem appendTapes_scratch (source destination scratch : K)
    (sourceScratch : source ≠ scratch) (destinationScratch : destination ≠ scratch)
    (base : K → List β) (scratchEmpty : base scratch = []) :
    appendTapes source destination base scratch = [] := by
  rw [appendTapes_other source destination scratch (Ne.symm sourceScratch)
    (Ne.symm destinationScratch) base, scratchEmpty]

private def firstTapes (destination scratch : K) (base : K → List β) : K → List β :=
  Reduction.MachineTransfer.tapesAt destination scratch base [] (base destination).reverse

private def secondTapes (source destination scratch : K) (base : K → List β) : K → List β :=
  Reduction.MachineTransfer.tapesAt source scratch (firstTapes destination scratch base) []
    ((base source).reverse ++ (base destination).reverse)

private theorem finalTapes_eq (source destination scratch : K)
    (sourceDestination : source ≠ destination) (sourceScratch : source ≠ scratch)
    (destinationScratch : destination ≠ scratch) (base : K → List β)
    (scratchEmpty : base scratch = []) :
    Reduction.MachineTransfer.tapesAt scratch destination
      (secondTapes source destination scratch base) [] (base destination ++ base source) =
        appendTapes source destination base := by
  funext k
  by_cases hs : k = source
  · subst k
    simp [appendTapes, secondTapes, firstTapes, Reduction.MachineTransfer.tapesAt,
      sourceDestination, sourceScratch]
  · by_cases hd : k = destination
    · subst k
      simp [appendTapes, Reduction.MachineTransfer.tapesAt]
    · by_cases ht : k = scratch
      · subst k
        simp [appendTapes, Reduction.MachineTransfer.tapesAt, Ne.symm sourceScratch,
          Ne.symm destinationScratch, scratchEmpty]
      · simp [appendTapes, secondTapes, firstTapes, Reduction.MachineTransfer.tapesAt,
          hs, hd, ht]

theorem appendTrace (source destination scratch : K)
    (sourceDestination : source ≠ destination) (sourceScratch : source ≠ scratch)
    (destinationScratch : destination ≠ scratch)
    (fallback : β) (firstLabel secondLabel thirdLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K) β) Λ (σ × Option β))
    (atFirst : program firstLabel = Reduction.MachineTransfer.loopAt destination scratch
      id fallback firstLabel (some secondLabel))
    (atSecond : program secondLabel = Reduction.MachineTransfer.loopAt source scratch
      id fallback secondLabel (some thirdLabel))
    (atThird : program thirdLabel = Reduction.MachineTransfer.loopAt scratch destination
      id fallback thirdLabel exit)
    (base : K → List β) (scratchEmpty : base scratch = [])
    (ambient : σ) (register : Option β) :
    (MachineComposition.advance (TM2.step program))^[
        2 * ((base source).length + (base destination).length) + 3]
      (some ⟨some firstLabel, (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), appendTapes source destination base⟩ := by
  have first := Reduction.MachineTransfer.transferAt_fromTapes destination scratch
    destinationScratch id fallback firstLabel (some secondLabel) program atFirst
    base ambient register
  change (MachineComposition.advance (TM2.step program))^[(base destination).length + 1]
    (some ⟨some firstLabel, (ambient, register), base⟩) = _ at first
  simp only [List.map_id, scratchEmpty, List.append_nil] at first
  change (MachineComposition.advance (TM2.step program))^[(base destination).length + 1]
    (some ⟨some firstLabel, (ambient, register), base⟩) =
      some ⟨some secondLabel, (ambient, none), firstTapes destination scratch base⟩ at first
  have firstSource : firstTapes destination scratch base source = base source := by
    simp [firstTapes, Reduction.MachineTransfer.tapesAt, sourceDestination, sourceScratch]
  have firstScratch : firstTapes destination scratch base scratch =
      (base destination).reverse := by
    simp [firstTapes]
  have second := Reduction.MachineTransfer.transferAt_fromTapes source scratch
    sourceScratch id fallback secondLabel (some thirdLabel) program atSecond
    (firstTapes destination scratch base) ambient none
  change (MachineComposition.advance (TM2.step program))^[
      (firstTapes destination scratch base source).length + 1]
    (some ⟨some secondLabel, (ambient, none), firstTapes destination scratch base⟩) = _
      at second
  rw [firstSource, firstScratch] at second
  simp only [List.map_id] at second
  change (MachineComposition.advance (TM2.step program))^[(base source).length + 1]
    (some ⟨some secondLabel, (ambient, none), firstTapes destination scratch base⟩) =
      some ⟨some thirdLabel, (ambient, none), secondTapes source destination scratch base⟩
        at second
  have secondScratch : secondTapes source destination scratch base scratch =
      (base source).reverse ++ (base destination).reverse := by
    simp [secondTapes]
  have secondDestination : secondTapes source destination scratch base destination = [] := by
    simp [secondTapes, firstTapes, Reduction.MachineTransfer.tapesAt,
      Ne.symm sourceDestination, destinationScratch]
  have third := Reduction.MachineTransfer.transferAt_fromTapes scratch destination
    (Ne.symm destinationScratch) id fallback thirdLabel exit program atThird
    (secondTapes source destination scratch base) ambient none
  change (MachineComposition.advance (TM2.step program))^[
      (secondTapes source destination scratch base scratch).length + 1]
    (some ⟨some thirdLabel, (ambient, none), secondTapes source destination scratch base⟩) = _
      at third
  rw [secondScratch, secondDestination] at third
  simp only [List.map_id, List.reverse_append, List.reverse_reverse, List.append_nil,
    List.length_append, List.length_reverse] at third
  rw [finalTapes_eq source destination scratch sourceDestination sourceScratch
    destinationScratch base scratchEmpty] at third
  rw [show 2 * ((base source).length + (base destination).length) + 3 =
      ((base source).length + (base destination).length + 1) +
        (((base source).length + 1) + ((base destination).length + 1)) by omega]
  rw [Function.iterate_add_apply]
  rw [Function.iterate_add_apply (m := (base source).length + 1)
    (n := (base destination).length + 1), first, second]
  exact third

/-- The timed witness stores the exact three-loop transition count. -/
def appendInTime (source destination scratch : K)
    (sourceDestination : source ≠ destination) (sourceScratch : source ≠ scratch)
    (destinationScratch : destination ≠ scratch)
    (fallback : β) (firstLabel secondLabel thirdLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K) β) Λ (σ × Option β))
    (atFirst : program firstLabel = Reduction.MachineTransfer.loopAt destination scratch
      id fallback firstLabel (some secondLabel))
    (atSecond : program secondLabel = Reduction.MachineTransfer.loopAt source scratch
      id fallback secondLabel (some thirdLabel))
    (atThird : program thirdLabel = Reduction.MachineTransfer.loopAt scratch destination
      id fallback thirdLabel exit)
    (base : K → List β) (scratchEmpty : base scratch = [])
    (ambient : σ) (register : Option β) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some firstLabel, (ambient, register), base⟩
      (some ⟨exit, (ambient, none), appendTapes source destination base⟩)
      (2 * ((base source).length + (base destination).length) + 3) where
  steps := 2 * ((base source).length + (base destination).length) + 3
  evals_in_steps := appendTrace source destination scratch sourceDestination sourceScratch
    destinationScratch fallback firstLabel secondLabel thirdLabel exit program atFirst
    atSecond atThird base scratchEmpty ambient register
  steps_le_m := Nat.le_refl _

end UniqueGamesTheorem.Foundations.Complexity.MachineAppendAt

end

end OAI
