import OAI.NumberTheory.Ostmann.Construction.InitialCoordinatesTemplateState
import OAI.NumberTheory.Ostmann.Construction.InitialEtaPrior
import OAI.NumberTheory.Ostmann.Construction.InitialSourceFamily

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction.InitialEta
open InitialCoordinatesTemplate

def initialSources (bulk : PrimeSource) {k : ℕ} (aux : AuxiliaryIndex k → PrimeSource)
    (b : ℕ) : SourceFamily :=
  initialSourceFamily b k bulk (fun i => aux (.inl i)) (fun j i => aux (.inr (j,i)))

def smallIndex (b k : ℕ) : SmallShape b k ≃ Fin (Template.initial (2*b) k).length :=
  (smallEquiv b k).trans (finCongr (initial_length (2*b) k).symm)

def smallPosition {b s k : ℕ} : SmallShape b k → Position b s (AuxiliaryIndex k)
  | .inl (h,i) => (h,.inr (.inl i))
  | .inr (.inl (h,i)) => (h,.inr (.inr (.inr (.inl i))))
  | .inr (.inr (j,(h,i))) => (h,.inr (.inr (.inr (.inr (j,i)))))

theorem initial_origin (b k : ℕ) (i : Fin (Template.initial (2*b) k).length) :
    (Template.initial (2*b) k)[i].origin = i.val := by
  change (List.ofFn (fun j : Fin (Template.initialRoles (2*b) k).length =>
    ({role := (Template.initialRoles (2*b) k)[j], origin := j.val} : SourceSlot)))[i.val].origin = i.val
  rw [List.getElem_ofFn]

theorem smallIndex_source (giant bulk spectator : PrimeSource) {b s k : ℕ}
    (aux : AuxiliaryIndex k → PrimeSource) (q : SmallShape b k) :
    initialSources bulk aux b ((Template.initial (2*b) k)[smallIndex b k q].origin) =
      tupleSource giant bulk spectator aux b s (smallPosition q) := by
  rw [initial_origin]
  change initialSourceValue b k bulk (fun i => aux (.inl i)) (fun j i => aux (.inr (j,i)))
    ((smallEquiv b k q).val) = _
  rcases q with ⟨h,i⟩ | (⟨h,i⟩ | ⟨j,h,i⟩)
  · rw [smallEquiv_bulk_val,initialSourceValue_bulk]
    · rfl
    · have hi := i.isLt
      cases h <;> simp <;> omega
  · rw [smallEquiv_top_val,initialSourceValue_top]
    rfl
  · rw [smallEquiv_compensation_val,initialSourceValue_comp]
    rfl

def sampleCast {S T : PrimeSource} (h : S=T) : S.Sample ≃ T.Sample :=
  Equiv.cast (congrArg PrimeSource.Sample h)

@[simp] theorem sampleCast_val {S T : PrimeSource} (h : S=T) (x : S.Sample) :
    (sampleCast h x : ℕ) = (x:ℕ) := by
  cases h
  rfl

@[simp] theorem sampleCast_mass {S T : PrimeSource} (h : S=T) (x : S.Sample) :
    T.law.mass (sampleCast h x) = S.law.mass x := by
  cases h
  rfl

def smallAssignmentEquiv (giant bulk spectator : PrimeSource) {b s k : ℕ}
    (aux : AuxiliaryIndex k → PrimeSource) :
    ((q : SmallShape b k) → (tupleSource giant bulk spectator aux b s (smallPosition q)).Sample) ≃
      SourceAssignment (initialSources bulk aux b) (Template.initial (2*b) k) :=
  (Equiv.piCongrRight (fun q => sampleCast (smallIndex_source giant bulk spectator aux q).symm)).trans
    (Equiv.piCongrLeft
      (fun i => (initialSources bulk aux b ((Template.initial (2*b) k)[i].origin)).Sample)
      (smallIndex b k))

@[simp] theorem smallAssignmentEquiv_apply (giant bulk spectator : PrimeSource) {b s k : ℕ}
    (aux : AuxiliaryIndex k → PrimeSource)
    (x : (q : SmallShape b k) → (tupleSource giant bulk spectator aux b s (smallPosition q)).Sample)
    (q : SmallShape b k) :
    (smallAssignmentEquiv giant bulk spectator aux x (smallIndex b k q) : ℕ) = (x q:ℕ) := by
  simp only [smallAssignmentEquiv,Equiv.trans_apply,Equiv.piCongrLeft_apply_apply,
    Equiv.piCongrRight_apply,Pi.map_apply,sampleCast_val]

theorem smallAssignmentEquiv_mass (giant bulk spectator : PrimeSource) {b s k : ℕ}
    (aux : AuxiliaryIndex k → PrimeSource)
    (x : (q : SmallShape b k) → (tupleSource giant bulk spectator aux b s (smallPosition q)).Sample) :
    (assignmentPrior (initialSources bulk aux b) (Template.initial (2*b) k)).mass
      (smallAssignmentEquiv giant bulk spectator aux x) =
    ∏q,(tupleSource giant bulk spectator aux b s (smallPosition q)).law.mass (x q) := by
  unfold assignmentPrior dependentProductPrior
  dsimp only
  rw [←(smallIndex b k).prod_comp]
  apply Finset.prod_congr rfl
  intro q hq
  simp only [smallAssignmentEquiv,Equiv.trans_apply,Equiv.piCongrLeft_apply_apply,
    Equiv.piCongrRight_apply,Pi.map_apply,sampleCast_mass]

end Ostmann.Construction.InitialEta

end

end OAI
