import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.HarmonicCongruenceBound
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.FirstSlot
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ExtFields
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.RowFactors
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.EdgeInjective
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.LinePrimeCode
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Spec

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.ArithmeticSaving OrdinaryCorrelations.SharedSlotPatterns
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.NumericalSubtrees Finset Classical
noncomputable section
variable {α β : Type*} [DecidableEq α] [DecidableEq β] {ℓ L J : ℕ}

abbrev GapPathCode (ℓ L : ℕ) := Fin L → Option (Fin ℓ × Bool)

namespace PatternExpression

def gap (h : ℕ) (sign : Fin ℓ → Bool) (c : Fin ℓ × Fin J → Option α)
    (path : GapPathCode ℓ L) : SquarefreeExpression α L where
  factors i := match path i with
    | none => ∅
    | some (e,_) => rowFactors (fun j => c (e,j))
  coefficient i := match path i with
    | none => 0
    | some (e,f) => (if f then 1 else -1)*(if sign e then 1 else -1)*(h:ℤ)

lemma gap_relabel (h : ℕ) (sign : Fin ℓ → Bool) (c : Fin ℓ × Fin J → Option α)
    (path : GapPathCode ℓ L) (v : α ↪ β) :
    (gap h sign c path).relabel v=gap h sign (fun s => (c s).map v) path := by
  apply SquarefreeExpression.ext_fields
  · funext i
    cases hp : path i with
    | none => simp [gap,SquarefreeExpression.relabel,hp]
    | some e =>
      simpa only [gap,SquarefreeExpression.relabel,hp] using
        (rowFactors_relabel (fun j => c (e.1,j)) v).symm
  · rfl
end PatternExpression

variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h : ℕ}
namespace TreePath
variable {w : NumericalLine D h ℓ}

def code (P : TreePath w L) : GapPathCode ℓ L := fun i =>
  if hi : i.val<P.length then some (P.edge ⟨i.val,hi⟩,P.forward ⟨i.val,hi⟩) else none

lemma code_source_factors (P : TreePath w L) (i : Fin L) :
    (PatternExpression.gap h (signBit w.line) w.linePrimeCode P.code).factors i =
      if hi : i.val<P.length then
        labelPrimeSet (w.line.label (P.edge ⟨i.val,hi⟩)) (w.labels _) else ∅ := by
  by_cases hi : i.val<P.length
  · simp only [PatternExpression.gap,code,dite_eq_left hi]
    change rowFactors (FiniteSlotEncoding.code
      (labelPrimeSet (w.line.label (P.edge ⟨i.val,hi⟩)) (w.labels _)) ⌈C₀*Real.log B⌉₊) =
      labelPrimeSet (w.line.label (P.edge ⟨i.val,hi⟩)) (w.labels _)
    apply rowFactors_code
    rw [labelPrimeSet_card]
    exact D.omega _ (w.labels _)
  · simp only [PatternExpression.gap,code,dite_eq_right hi]

lemma code_source_coefficient (P : TreePath w L) (i : Fin L) :
    (PatternExpression.gap h (signBit w.line) w.linePrimeCode P.code).coefficient i =
      if hi : i.val<P.length then
        if 0 ≤ i.val ∧ i.val<P.length then P.pathSign ⟨i.val,hi⟩*(h:ℤ) else 0
      else 0 := by
  by_cases hi : i.val<P.length
  · simp only [PatternExpression.gap,code,Nat.zero_le,true_and,hi,ite_true,dite_true]
    rw [←signBit_decode w.line (P.edge ⟨i.val,hi⟩)]
    cases hf : P.forward ⟨i.val,hi⟩ <;> simp [pathSign,hf]
  · simp only [PatternExpression.gap,code,dite_eq_right hi]

lemma code_source (P : TreePath w L) (p : S.Index)
    (hfree : ∀ i, ¬(p:ℕ) ∣ w.line.label (P.edge i))
    (hd : ((p:ℕ):ℤ) ∣ P.vertex (Fin.last P.length)-P.vertex 0) :
    PatternExpression.gap h (signBit w.line) w.linePrimeCode P.code =
      (P.specification p hfree hd).segmentExpression 0 P.length := by
  apply SquarefreeExpression.ext_fields
  · funext i
    exact P.code_source_factors i
  · funext i
    exact P.code_source_coefficient i

end TreePath

namespace GapFamily
variable {w : NumericalLine D h ℓ} {a : S.FixedResidues w.line} {t : ℕ}
variable (F : GapFamily w a L t)
lemma pattern_source (j : Fin t) :
    PatternExpression.gap h (signBit w.line) w.linePrimeCode (F.path j).code = F.expression j :=
  (F.path j).code_source (F.modulus j).val _ _
end GapFamily

end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
