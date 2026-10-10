import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Symbolic
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.WitnessConfiguration
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SpecSegment
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.RelabelAppend

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.NumericalSubtrees
open OrdinaryCorrelations.ArithmeticSaving OrdinaryCorrelations.SharedSlotPatterns
open Finset Classical

structure WitnessTestShape (ℓ L t : ℕ) where
  witness : Fin t
  other : Fin t
  compare : Bool
  a : Fin (L+1)
  b : Fin (L+1)
  c : Fin (L+1)
  lineA : Fin (ℓ+1)
  lineB : Fin (ℓ+1)
  deriving DecidableEq

namespace WitnessTestShape
noncomputable def equiv (ℓ L t : ℕ) : WitnessTestShape ℓ L t ≃
    Fin t × Fin t × Bool × Fin (L+1) × Fin (L+1) × Fin (L+1) × Fin (ℓ+1) × Fin (ℓ+1) :=
  { toFun d := (d.witness,d.other,d.compare,d.a,d.b,d.c,d.lineA,d.lineB)
    invFun z := ⟨z.1,z.2.1,z.2.2.1,z.2.2.2.1,z.2.2.2.2.1,z.2.2.2.2.2.1,
      z.2.2.2.2.2.2.1,z.2.2.2.2.2.2.2⟩
    left_inv _ := rfl
    right_inv _ := rfl }
noncomputable instance (ℓ L t : ℕ) : Fintype (WitnessTestShape ℓ L t) :=
  Fintype.ofEquiv _ (equiv ℓ L t).symm

variable {α β : Type*} [DecidableEq α] [DecidableEq β] {ℓ L J t : ℕ}

noncomputable def expression (d : WitnessTestShape ℓ L t) (h : ℕ)
    (m : WitnessMetadata ℓ L t) (p : WitnessCodeSlot ℓ L J t → Option α) :
    SquarefreeExpression α ((ℓ+L)+L) :=
  if d.compare then
    ((PatternExpression.lineSegment h m.1 (fun k => p (.inl k)) d.lineA d.lineB).append
      (PatternExpression.specSegment h (m.2.2 d.witness).2
        (fun k => p (.inr (.inr (.inl (d.witness,k))))) d.a.val d.b.val)).append
      (PatternExpression.specSegment h (m.2.2 d.other).2
        (fun k => p (.inr (.inr (.inl (d.other,k))))) 0 d.c.val).neg
  else ((SquarefreeExpression.zeroExpression α ℓ).append
      (PatternExpression.specSegment h (m.2.2 d.witness).2
        (fun k => p (.inr (.inr (.inl (d.witness,k))))) d.a.val d.b.val)).append
      (SquarefreeExpression.zeroExpression α L)

lemma expression_relabel (d : WitnessTestShape ℓ L t) (h : ℕ)
    (m : WitnessMetadata ℓ L t) (p : WitnessCodeSlot ℓ L J t → Option α) (e : α ↪ β) :
    (d.expression h m p).relabel e=d.expression h m (fun s => (p s).map e) := by
  unfold expression
  split_ifs <;> simp only [SquarefreeExpression.relabel_append,
    SquarefreeExpression.relabel_neg,SquarefreeExpression.relabel_zero,
    PatternExpression.specSegment_relabel,PatternExpression.lineSegment_relabel]

lemma card (ℓ L t : ℕ) :
    Fintype.card (WitnessTestShape ℓ L t)=t^2*2*(L+1)^3*(ℓ+1)^2 := by
  rw [Fintype.card_congr (equiv ℓ L t)]
  simp only [Fintype.card_prod,Fintype.card_bool,Fintype.card_fin]
  ring
end WitnessTestShape

variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L t : ℕ}
namespace WitnessConfiguration
variable (x : WitnessConfiguration D h ℓ L t)

noncomputable def shape {j : Fin t} : x.family.Test j → WitnessTestShape ℓ L t
  | .extra | .tail _ =>
    { witness := j, other := j, compare := false
      a := ⟨(x.family.witness j).spec.suffix.val,by
        have := (x.family.witness j).spec.suffix.isLt
        have := (x.family.witness j).spec.length_le
        omega⟩
      b := ⟨(x.family.witness j).spec.length,Nat.lt_succ_of_le (x.family.witness j).spec.length_le⟩
      c := 0, lineA := 0, lineB := 0 }
  | .compare i _ r hi =>
    { witness := j, other := i, compare := true
      a := 0
      b := ⟨(x.family.witness j).spec.tailStart.val,by
        have := (x.family.witness j).spec.tailStart.isLt
        have := (x.family.witness j).spec.length_le
        omega⟩
      c := ⟨((x.family.witness i).spec.activity r hi).val,by
        have := ((x.family.witness i).spec.activity r hi).isLt
        have := (x.family.witness i).spec.length_le
        omega⟩
      lineA := (x.family.witness i).index
      lineB := (x.family.witness j).index }

lemma shape_expression {j : Fin t} (d : x.family.Test j) :
    (x.shape d).expression h x.metadata x.primeCode=d.symbolic x.labels := by
  have hs (j : Fin t) (a b : ℕ) :
      PatternExpression.specSegment h (x.metadata.2.2 j).2
        (fun k => x.primeCode (.inr (.inr (.inl (j,k))))) a b =
      (x.family.witness j).spec.segmentExpression a b :=
    PatternExpression.specSegment_source _ a b
  have hl (a b : Fin (ℓ+1)) :
      PatternExpression.lineSegment h x.metadata.1 (fun k => x.primeCode (.inl k)) a b=
      LineExpression.segment x.line x.labels a b :=
    PatternExpression.lineSegment_source x.line x.labels a b
  cases d with
  | extra | tail => simp only [shape,WitnessTestShape.expression,Bool.false_eq_true,ite_false,
      hs,PrivateFamily.Test.symbolic]
  | compare i q r hi => simp only [shape,WitnessTestShape.expression,ite_true,Fin.val_zero,
      hs,hl,PrivateFamily.Test.symbolic]

lemma pattern_shape_expression {j : Fin t} (d : x.family.Test j) :
    ((x.shape d).expression h x.metadata (pattern x.primeCode)).relabel (values x.primeCode)=
      d.symbolic x.labels := by
  rw [WitnessTestShape.expression_relabel]
  simp only [decode_pattern]
  exact x.shape_expression d

end WitnessConfiguration
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
