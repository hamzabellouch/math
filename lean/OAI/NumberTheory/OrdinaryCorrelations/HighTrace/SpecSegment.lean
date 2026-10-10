import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Topology
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.EdgeAt
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.FirstSlot
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ExtFields
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.RowFactors

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem.PatternExpression
open OrdinaryCorrelations.ArithmeticSaving OrdinaryCorrelations.SharedSlotPatterns
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.NumericalSubtrees Finset Classical
variable {α β : Type*} [DecidableEq α] [DecidableEq β] {ℓ L J : ℕ}

noncomputable def specSegment (h : ℕ) (m : SpecMetadata L) (c : SpecCodeSlot L J → Option α)
    (a b : ℕ) : SquarefreeExpression α L where
  factors i := rowFactors (fun j => c (some (i,j)))
  coefficient i := if i.val < m.1.val then
    if a ≤ i.val ∧ i.val<b then (if m.2.1 i then 1 else -1)*(h:ℤ) else 0
    else 0

noncomputable def lineSegment (h : ℕ) (m : Fin ℓ → Bool)
    (c : Fin ℓ × Fin J → Option α) (a b : Fin (ℓ+1)) : SquarefreeExpression α ℓ where
  factors i := rowFactors (fun j => c (i,j))
  coefficient i := if min a.val b.val ≤ i.val ∧ i.val < max a.val b.val then
    (if a ≤ b then 1 else -1)*(if m i then 1 else -1)*(h:ℤ) else 0

lemma specSegment_relabel (h : ℕ) (m : SpecMetadata L) (c : SpecCodeSlot L J → Option α)
    (a b : ℕ) (e : α ↪ β) :
    (specSegment h m c a b).relabel e =
      specSegment h m (fun s => (c s).map e) a b := by
  apply SquarefreeExpression.ext_fields
  · funext i
    exact (rowFactors_relabel _ e).symm
  · rfl

lemma lineSegment_relabel (h : ℕ) (m : Fin ℓ → Bool)
    (c : Fin ℓ × Fin J → Option α) (a b : Fin (ℓ+1)) (e : α ↪ β) :
    (lineSegment h m c a b).relabel e =
      lineSegment h m (fun s => (c s).map e) a b := by
  apply SquarefreeExpression.ext_fields
  · funext i
    exact (rowFactors_relabel _ e).symm
  · rfl

variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h : ℕ}

lemma specSegment_source (s : S.Specification D h L) (a b : ℕ) :
    specSegment h (specMetadata s) (specPrimeCode s) a b=s.segmentExpression a b := by
  apply SquarefreeExpression.ext_fields
  · funext i
    by_cases hi : i.val<s.length
    · change rowFactors (fun j => if hj : i.val<s.length then
        FiniteSlotEncoding.code (labelPrimeSet (s.label ⟨i.val,hj⟩) (s.label_mem _)) _ j
        else none)=_
      simp only [dite_eq_left hi,Specification.segmentExpression]
      apply rowFactors_code
      rw [labelPrimeSet_card]
      exact D.omega _ (s.label_mem _)
    · simp only [specSegment,specPrimeCode,Specification.segmentExpression,dite_eq_right hi,
        rowFactors,Option.toFinset_none]
      ext p
      simp
  · funext i
    by_cases hi : i.val<s.length
    · change (if i.val<s.length then _ else _) = _
      simp only [ite_eq_left hi,specMetadata,dite_eq_left hi,Specification.segmentExpression]
      rcases s.sign_mem ⟨i.val,hi⟩ with hs|hs <;> simp [hs]
    · simp [specSegment,specMetadata,Specification.segmentExpression,hi]

lemma lineSegment_source (w : ClosedLine h ℓ) (hl : ∀ i, w.label i ∈ D.members)
    (a b : Fin (ℓ+1)) :
    lineSegment h (signBit w)
      (fun k => FiniteSlotEncoding.code (labelPrimeSet (w.label k.1) (hl k.1)) ⌈C₀*Real.log B⌉₊ k.2)
      a b = LineExpression.segment w hl a b := by
  apply SquarefreeExpression.ext_fields
  · funext i
    change rowFactors (FiniteSlotEncoding.code (labelPrimeSet (w.label i) (hl i))
      ⌈C₀*Real.log B⌉₊) = labelPrimeSet (w.label i) (hl i)
    apply rowFactors_code
    rw [labelPrimeSet_card]
    exact D.omega _ (hl i)
  · funext i
    simp only [lineSegment,LineExpression.segment,←signBit_decode w]

end OrdinaryCorrelations.GraphKernel.PrimeSystem.PatternExpression

end

end OAI
