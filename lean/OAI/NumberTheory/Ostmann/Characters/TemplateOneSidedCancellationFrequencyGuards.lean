import Mathlib.Data.ZMod.Units
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationResidues
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationSampled

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedCancellation
open SymbolicHistory Template
attribute [local instance] Classical.propDecidable
variable {ι : Type*}

theorem unit_natAbs_iff (x s : ℤ) :
    IsUnit (x : ZMod s.natAbs) ↔ IsCoprime s x := by
  rw [ZMod.coe_int_isUnit_iff_isCoprime,Int.isCoprime_iff_nat_coprime,
    Int.isCoprime_iff_nat_coprime,Int.natAbs_natCast]

def rootResidueGuards (k j : ℕ) (s : ℤ) (e : Expressions (ι:=ι) k j) :
    List (ResidueGuard ι) :=
  List.ofFn (fun i : Fin (Fintype.card (schedule k j).Slot) =>
    ⟨e ((Fintype.equivFin (schedule k j).Slot).symm i),s.natAbs⟩)

theorem rootResidueGuards_holds (k j : ℕ) (s : ℤ)
    (e : Expressions (ι:=ι) k j) (a : ι → ℤ) :
    (∀ q ∈ rootResidueGuards k j s e, q.holds a) ↔
      ∀ i, (e i).IntegralAt a ∧ IsCoprime s (evalExpressions a e i) := by
  constructor
  · intro h i
    have hm : (⟨e i,s.natAbs⟩ : ResidueGuard ι) ∈ rootResidueGuards k j s e := by
      apply List.mem_ofFn.mpr
      exact ⟨(Fintype.equivFin (schedule k j).Slot) i,by simp⟩
    exact ⟨(h _ hm).1,(unit_natAbs_iff _ _).mp (h _ hm).2⟩
  · intro h q hq
    obtain ⟨n,rfl⟩ := List.mem_ofFn.mp hq
    exact ⟨(h _).1,(unit_natAbs_iff _ _).mpr (h _).2⟩

theorem rootResidueGuards_valid (k j : ℕ) (s : ℤ)
    (e : Expressions (ι:=ι) k j) (hs : s ≠ 0) (he : ∀ i, (e i).Valid) :
    ∀ q ∈ rootResidueGuards k j s e, q.Valid := by
  intro q hq
  obtain ⟨n,rfl⟩ := List.mem_ofFn.mp hq
  exact ⟨he _,Int.natAbs_pos.mpr hs⟩

def nodeResidueGuards (k j : ℕ) (e : Expressions (ι:=ι) k (j+1)) (s v w : ℤ) :
    List (ResidueGuard ι) :=
  [⟨pivotExpression k j e s v w,w.natAbs⟩,
   ⟨copiedExpression k j true e,s.natAbs⟩,
   ⟨copiedExpression k j false e,s.natAbs⟩]

theorem copiedExpression_good (k j : ℕ) (b : Bool)
    (e : Expressions (ι:=ι) k (j+1)) (a : ι → ℤ)
    (he : ∀ i, HistoryReconstruction.Good a (e i)) :
    HistoryReconstruction.Good a (copiedExpression k j b e) :=
  finiteProductExpression_good _ a (fun _ => he _)

theorem pivotExpression_integral_iff (k j : ℕ)
    (e : Expressions (ι:=ι) k (j+1)) (s v w : ℤ) (a : ι → ℤ)
    (he : ∀ i, HistoryReconstruction.Good a (e i)) :
    (pivotExpression k j e s v w).IntegralAt a ↔
      s ∣ v*copiedProduct k j false (evalExpressions a e)-
        w*copiedProduct k j true (evalExpressions a e) := by
  have hL := (copiedExpression_good k j true e a he).2
  have hR := (copiedExpression_good k j false e a he).2
  simp only [pivotExpression,Expr.IntegralAt,hL,hR,true_and,and_self,Expr.integerEval,
    copiedExpression_eval]

theorem nodeResidueGuards_holds (k j : ℕ) (e : Expressions (ι:=ι) k (j+1))
    (s v w V : ℤ) (a : ι → ℤ) (he : ∀ i, HistoryReconstruction.Good a (e i))
    (hs : s ≠ 0) (hv : |v| ≤ V) (hw : |w| ≤ V) :
    (∀ q ∈ nodeResidueGuards k j e s v w, q.holds a) ↔
      NodeArithmetic k j (evalExpressions a e) s v w V ∧
        IntegerNodeSupport k j s v w (evalExpressions a e) := by
  have hL := (copiedExpression_good k j true e a he).2
  have hR := (copiedExpression_good k j false e a he).2
  simp only [nodeResidueGuards,List.forall_mem_cons,
    ResidueGuard.holds,pivotExpression_integral_iff k j e s v w a he,hL,hR,true_and,
    pivotExpression_eval,copiedExpression_eval]
  simp only [List.not_mem_nil,IsEmpty.forall_iff,implies_true,and_true]
  constructor
  · rintro ⟨⟨hi,hP⟩,hlu,hru⟩
    exact ⟨⟨hs,hv,hw,hi,(unit_natAbs_iff _ _).mp hru,
      ((unit_natAbs_iff _ _).mp hP).symm⟩,⟨hi,hlu,hru⟩⟩
  · rintro ⟨h,hi⟩
    exact ⟨⟨h.integral,(unit_natAbs_iff _ _).mpr h.pivot_unit.symm⟩,
      hi.left_unit,hi.right_unit⟩

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
