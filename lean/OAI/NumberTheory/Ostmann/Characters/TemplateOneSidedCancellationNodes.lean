import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationSubstitution

namespace OAI

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedCancellation
open SymbolicHistory Template
variable {ι : Type*}

def nodeGuards (k j : ℕ) (e : Expressions (ι:=ι) k (j+1)) (s v w B V : ℤ) : List (Guard ι) :=
  [⟨copiedExpression k j false e,0,true,true⟩,
   ⟨pivotExpression k j e s v w,0,true,true⟩,
   ⟨pivotExpression k j e s v w,(B:ℝ),false,false⟩,
   ⟨copiedExpression k j false e,((2*B*V:ℤ):ℝ),true,true⟩]

theorem nodeGuards_holds (k j : ℕ) (e : Expressions (ι:=ι) k (j+1))
    (s v w B V : ℤ) (a : ι → ℤ) :
    guardsHold (nodeGuards k j e s v w B V) a ↔
      0 < copiedProduct k j false (evalExpressions a e) ∧
      0 < reconstructedPivot k j (evalExpressions a e) s v w ∧
      reconstructedPivot k j (evalExpressions a e) s v w ≤ B ∧
      2*B*V < copiedProduct k j false (evalExpressions a e) := by
  simp only [guardsHold,nodeGuards,List.forall_mem_cons,
    Guard.holds,ite_true,Bool.false_eq_true,ite_false,copiedExpression_eval,pivotExpression_eval]
  norm_cast
  simp

structure NodeArithmetic (k j : ℕ) (x : State k (j+1)) (s v w V : ℤ) : Prop where
  root_ne_zero : s ≠ 0
  left_frequency_le : |v| ≤ V
  right_frequency_le : |w| ≤ V
  integral : s ∣ v*copiedProduct k j false x-w*copiedProduct k j true x
  root_unit : IsCoprime s (copiedProduct k j false x)
  pivot_unit : IsCoprime (reconstructedPivot k j x s v w) w

theorem nodeSupported_iff (k j : ℕ) (e : Expressions (ι:=ι) k (j+1))
    (s v w B V : ℤ) (a : ι → ℤ) :
    NodeSupported k j (evalExpressions a e) s v w B V ↔
      NodeArithmetic k j (evalExpressions a e) s v w V ∧
        guardsHold (nodeGuards k j e s v w B V) a := by
  rw [nodeGuards_holds]
  constructor
  · intro h
    exact ⟨⟨h.root_ne_zero,h.left_frequency_le,h.right_frequency_le,h.integral,h.root_unit,h.pivot_unit⟩,
      h.right_pos,h.pivot_pos,h.pivot_le,h.range_gap⟩
  · rintro ⟨h,hr,hp,hB,hgap⟩
    exact ⟨h.root_ne_zero,hr,hp,hB,h.left_frequency_le,h.right_frequency_le,hgap,
      h.integral,h.root_unit,h.pivot_unit⟩

def positiveGuards (k j : ℕ) (e : Expressions (ι:=ι) k j) : List (Guard ι) :=
  List.ofFn (fun i : Fin (Fintype.card (schedule k j).Slot) =>
    ⟨e ((Fintype.equivFin (schedule k j).Slot).symm i),0,true,true⟩)

theorem positiveGuards_holds (k j : ℕ) (e : Expressions (ι:=ι) k j) (a : ι → ℤ) :
    guardsHold (positiveGuards k j e) a ↔ ∀ i, 0 < evalExpressions a e i := by
  constructor
  · intro h i
    let f : Fin (Fintype.card (schedule k j).Slot) → Guard ι :=
      fun n => ⟨e ((Fintype.equivFin (schedule k j).Slot).symm n),0,true,true⟩
    have hm : (⟨e i,0,true,true⟩ : Guard ι) ∈ positiveGuards k j e := by
      apply List.mem_ofFn.mpr
      exact ⟨(Fintype.equivFin (schedule k j).Slot) i,by simp⟩
    have hh := h _ hm
    change (0:ℝ) < (Expr.integerEval a (e i):ℝ) at hh
    exact_mod_cast hh
  · intro h q hq
    obtain ⟨n,rfl⟩ := List.mem_ofFn.mp hq
    change (0:ℝ) < (Expr.integerEval a (e ((Fintype.equivFin (schedule k j).Slot).symm n)):ℝ)
    exact_mod_cast h ((Fintype.equivFin (schedule k j).Slot).symm n)

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
