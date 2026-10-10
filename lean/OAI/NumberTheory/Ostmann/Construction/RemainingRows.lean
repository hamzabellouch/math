import OAI.NumberTheory.Ostmann.Construction.AssignmentReinsert
import OAI.NumberTheory.Ostmann.Construction.CountedRows
import OAI.NumberTheory.Ostmann.Construction.FavorableHalfRows

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction

abbrev RemainingSample (sources : SourceFamily) (T : List SourceSlot) (giant : PrimeSource) :=
  giant.Sample×SourceAssignment sources T

def remainingPrior (sources : SourceFamily) (T : List SourceSlot) (giant : PrimeSource) :
    FinitePrior (RemainingSample sources T giant) := giant.law.pair (assignmentPrior sources T)

def remainingState (sources : SourceFamily) (T : List SourceSlot) (j : ℕ)
    (giant : PrimeSource) (p : ℕ) (u : SourceAssignment sources (Template.extracted j T))
    (y : RemainingSample sources (Template.remainder j T) giant) (v : ℤ) : State :=
  ⟨v,p,y.1.val,Template.reinsert j T (assignedSlots sources (Template.extracted j T) u)
    (assignedSlots sources (Template.remainder j T) y.2)⟩

def remainingProduct (sources : SourceFamily) (T : List SourceSlot) (giant : PrimeSource)
    (y : RemainingSample sources T giant) : ℕ := halfProduct y.1.val (assignedSlots sources T y.2)

def remainingIntegrand (d : Decomposition) (P : Finset ℕ) (sources : SourceFamily)
    (seed : List SourceSlot) (V : ℕ→ℕ) (giant : PrimeSource) (X G : ℝ)
    (bins : List ℕ→State→ℝ) (outside : List ℕ) (l p : ℕ)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)))
    (y : RemainingSample sources (Template.remainder (l+1) (Template.current seed l)) giant)
    (v : AllowedFrequency V l) : ℂ :=
  let T := Template.current seed l
  let us := assignedSlots sources (Template.extracted (l+1) T) u
  let hs := assignedSlots sources (Template.remainder (l+1) T) y.2
  halfTransform (residueTransform d) (favorableGiantResidueTransform d P)
    (outsideProduct outside*halfProduct p us) v.val y.1.val hs *
      actualCoefficient sources seed V X G (residueTransform d) bins outside l
        (remainingState sources T (l+1) giant p u y v.val)

def remainingRow (d : Decomposition) (P : Finset ℕ) (sources : SourceFamily)
    (seed : List SourceSlot) (V : ℕ→ℕ) (giant : PrimeSource) (X G : ℝ)
    (bins : List ℕ→State→ℝ) (outside : List ℕ) (l p : ℕ)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)))
    (t : ZMod (halfProduct p (assignedSlots sources (Template.extracted (l+1) (Template.current seed l)) u))) : ℂ :=
  let T := Template.current seed l
  let us := assignedSlots sources (Template.extracted (l+1) T) u
  countedGroupedRow (remainingPrior sources (Template.remainder (l+1) T) giant)
    (fun y (v : AllowedFrequency V l) =>
      modFraction (halfProduct p us) v.val (remainingProduct sources (Template.remainder (l+1) T) giant y))
    (remainingIntegrand d P sources seed V giant X G bins outside l p u) t

theorem remainingRow_pairing (d : Decomposition) (P : Finset ℕ) (sources : SourceFamily)
    (seed : List SourceSlot) (V : ℕ→ℕ) (giant : PrimeSource) (X G : ℝ)
    (bins : List ℕ→State→ℝ) (outside : List ℕ) (l p : ℕ) (hp : 0<p)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)))
    [NeZero (halfProduct p (assignedSlots sources (Template.extracted (l+1) (Template.current seed l)) u))] :
    (∑t,guardedFavorableHalfRow d P (outsideProduct outside) p
        (assignedSlots sources (Template.extracted (l+1) (Template.current seed l)) u) t *
      remainingRow d P sources seed V giant X G bins outside l p u t) =
    giant.law.cmean (fun q =>
      (assignmentPrior sources (Template.remainder (l+1) (Template.current seed l))).cmean (fun h =>
        ∑v:AllowedFrequency V l,
          let a := remainingState sources (Template.current seed l) (l+1) giant p u (q,h) v.val
          regularTransform (residueTransform d) (favorableGiantResidueTransform d P) outside a *
            actualCoefficient sources seed V X G (residueTransform d) bins outside l a)) := by
  unfold remainingRow
  dsimp only
  rw [countedGroupedRow_pairing,remainingPrior,FinitePrior.pair_cmean]
  apply congrArg (FinitePrior.cmean giant.law)
  funext q
  apply congrArg (FinitePrior.cmean (assignmentPrior sources (Template.remainder (l+1) (Template.current seed l))))
  funext h
  apply Finset.sum_congr rfl
  intro v hv
  exact (actualCoefficient_row_factorization d P sources seed V X G bins outside l
    (remainingState sources (Template.current seed l) (l+1) giant p u (q,h) v.val)
    (assignedSlots sources (Template.extracted (l+1) (Template.current seed l)) u)
    (assignedSlots sources (Template.remainder (l+1) (Template.current seed l)) h)
    (Template.reinsert_perm _ _ _ _ (assignedSlots_length _ _ _) (assignedSlots_length _ _ _))
    hp (giant.prime _ q.property).pos
    (fun z hz => (assignedSlots_prime _ _ u z hz).pos)
    (fun z hz => (assignedSlots_prime _ _ h z hz).pos)).symm

end Ostmann.Construction

end

end OAI
