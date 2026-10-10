import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipalDensity
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkUniversalPatternAggregationFamily

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceLaws HistoryBulkSourceDisintegration HistoryBulkReferenceFrequencyFamily
open HistoryBulkUniversalPatternAggregation HistoryBulkSelectedUniversalOperator
open HistoryBulkFibreGiantApproximation
attribute [local instance] Classical.propDecidable
local instance universalPrincipalBasicInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
    {C : InitialSourceChoice d Bs BD Bz k L E} {outside : List ℕ}

def withDensity
    {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}
    (family : SymbolicPatternFamily C outside l p) (mixed : Bool) :
    SymbolicPatternFamily C outside l p :=
  { family with
    mask := fun i=>assignmentDensity (family.data i).assignment mixed
    mask_mem := fun i=>assignmentDensity_mem (family.data i).assignment mixed }

theorem prior_nonempty {α : Type*} [Fintype α] (μ : FinitePrior α) : Nonempty α := by
  by_contra h
  let : IsEmpty α := not_nonempty_iff.mp h
  have ht := μ.mass_total
  simp only [Finset.univ_eq_empty,Finset.sum_empty] at ht
  norm_num at ht

def emptyFamily (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
    (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)) :
    SymbolicPatternFamily C outside l p := by
  let x := Classical.choice (prior_nonempty
    (internalSourcePrior C.sources (Template.initial (2*(bulkSize k L/2)) k) l))
  refine { permutation := Equiv.refl _
           left := x
           right := x
           refs := fun _=>none
           data := ?_
           representative := ?_
           mask := fun _=>0
           mask_mem := fun _=>⟨le_rfl,zero_le_one⟩ }
  · intro i
    exact False.elim (by simpa using i.property)
  · intro i
    exact False.elim (by simpa using i.property)

@[simp] theorem emptyFamily_value (C : InitialSourceChoice d Bs BD Bz k L E)
    (outside : List ℕ)
    (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
    (b : Block p → CommonSample C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l))
    (mixed : Bool) (s : ℕ) (hp : ∀q∈outside,q.Prime)
    (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q) :
    (emptyFamily C outside p).value b mixed s hp hV = 0 := by
  unfold SymbolicPatternFamily.value
  apply Finset.sum_eq_zero
  intro i _
  unfold presentComplexValue
  exact dite_eq_right Bool.false_ne_true

end Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal

end

end OAI
