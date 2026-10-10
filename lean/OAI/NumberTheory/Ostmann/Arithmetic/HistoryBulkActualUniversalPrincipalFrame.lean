import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipalDensity
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreIntegralReplacementFrameWeighted
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIdentityFrequencyRootTest
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSelectedUniversalOperatorActualDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal
open Construction Conclusion HistoryBulkReferenceFrequencyFamily HistoryBulkSelectedUniversalOperator
open HistoryBulkGiantIntegerReference HistoryBulkFibreGiantApproximation HistoryBulkGoodPatternPrincipalFrame
open HistoryBulkFibreIntegralReplacementFrame HistoryBulkSourceDisintegration
open HistoryBulkSelectedIntegralReplacement ResidueHaar
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  {C : InitialSourceChoice d Bs BD Bz k L E} {outside : List ℕ}
  {σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2)))}
  {x y : InternalSourceDraws C.sources (Template.initial (2*(bulkSize k L/2)) k) l}
  {i : RootFrequencyIndex (frequencyBound Bs BD Bz k L) l}
  {r : SupportedReference C.sources (Template.initial (2*(bulkSize k L/2)) k)
    (frequencyBound Bs BD Bz k L) outside l x y i.1.val i.1.val i.2}

def frameOfData (a : ActualReferenceData C σ i r) (hp : ∀q∈outside,q.Prime) :
    Frame (l:=l) C outside where
  leftSource := a.assignment
  rightSource := permutedAssignment C l σ a.assignment
  s := i.1.val
  t := i.1.val
  P := a.plus
  Q := a.minus
  leftChoices := assembleHistoryChoices C.sources _ _ l i.2.1 x
  rightChoices := assembleHistoryChoices C.sources _ _ l i.2.2 y
  left_mass := a.assignment_mass
  right_mass := by rw [permutedAssignment_mass]; exact a.assignment_mass
  left_choices_mass := a.left_choice_mass
  right_choices_mass := a.right_choice_mass
  plus_pos := a.plus_pos
  minus_pos := a.minus_pos
  plus_cell := a.plus_cell
  minus_cell := a.minus_cell
  left_supported := actualReference_left_supported C a
  right_supported := actualReference_right_supported C a
  matching := integerMatching C _ l σ a.assignment i.1.val i.1.val a.plus a.minus _ _
  outside_primes := hp

theorem frameOfData_left (a : ActualReferenceData C σ i r) (hp : ∀q∈outside,q.Prime) :
    (frameOfData a hp).left = decodeHistory C.sources _ _ l r.left
      (assembleHistoryChoices C.sources _ _ l i.2.1 x) := by
  rw [a.left_eq]
  rfl

theorem frameOfData_right (a : ActualReferenceData C σ i r) (hp : ∀q∈outside,q.Prime) :
    (frameOfData a hp).right = decodeHistory C.sources _ _ l r.right
      (assembleHistoryChoices C.sources _ _ l i.2.2 y) := by
  rw [a.right_eq]
  rfl

theorem frameOfData_integral (a : ActualReferenceData C σ i r)
    (hp : ∀q∈outside,q.Prime) (mixed : Bool) :
    principalIntegral (frameOfData a hp) false mixed =
      actualNestedIntegral C mixed (bulkSize k L/2) a := by
  cases mixed <;> rfl

theorem frameOfData_operator (a : ActualReferenceData C (Equiv.refl _) i r)
    (hp : ∀q∈outside,q.Prime) (mixed : Bool)
    (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q) :
    principalOperator (frameOfData a hp) false mixed (Equiv.refl _) hV =
      actualNestedIntegral C mixed (bulkSize k L/2) a *
        referenceRootAverage mixed d k (2*(bulkSize k L/2)) (Equiv.refl _) hp hV r := by
  let : NeZero (HistoryBulkReplacementGeometry.bulkModulus
      (frameOfData a hp).left (frameOfData a hp).right outside k) :=
    ⟨HistoryBulkResidueNormSum.actual_bulk_modulus_ne_zero _ _
      (frameOfData a hp).left_supported (frameOfData a hp).right_supported hp k⟩
  unfold principalOperator
  dsimp only
  rw [frameOfData_integral]
  apply congrArg (fun z=>actualNestedIntegral C mixed (bulkSize k L/2) a*z)
  rcases r with ⟨rl,rr,rf,sf,rm,sm,rs,ss⟩
  rcases a with ⟨ax,ap,aq,am,ac,ae,ap0,aq0,apc,aqc,al,ar⟩
  dsimp only at al ar
  subst rl
  subst rr
  unfold referenceRootAverage
  dsimp only
  apply congrArg average
  funext z
  exact HistoryBulkIdentityFrequency.rootTest_identity mixed d _ _ _ _ hp hV k z

theorem frameOfData_operator_of_identity (a : ActualReferenceData C σ i r)
    (hσ : σ=Equiv.refl _) (hp : ∀q∈outside,q.Prime) (mixed : Bool)
    (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q) :
    principalOperator (frameOfData a hp) false mixed σ hV =
      actualNestedIntegral C mixed (bulkSize k L/2) a *
        referenceRootAverage mixed d k (2*(bulkSize k L/2)) σ hp hV r := by
  subst σ
  exact frameOfData_operator a hp mixed hV

theorem frameOfData_density (a : ActualReferenceData C σ i r)
    (hp : ∀q∈outside,q.Prime) (mixed : Bool) :
    (assignmentDensity a.assignment mixed : ℂ) = rootDensity (frameOfData a hp) mixed := by
  rw [assignmentDensity_cast]
  rfl

end Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal

end

end OAI
