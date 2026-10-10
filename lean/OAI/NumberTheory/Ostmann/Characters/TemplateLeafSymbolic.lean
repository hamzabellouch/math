import OAI.NumberTheory.Ostmann.Characters.TemplateSymbolic
import OAI.NumberTheory.Ostmann.Characters.TemplateWeightProfiles

namespace OAI

noncomputable section
namespace Ostmann.Characters.Template
open SymbolicHistory
variable {ι:Type*}

abbrev BottomExpression (k:ℕ) := Bool×ℤ×Expressions (ι:=ι) k 0

def bottomExpressions (k:ℕ) : (j:ℕ)→Bool→ℤ→Expressions (ι:=ι) k j→
    HistoryReconstruction.Tree j→List (BottomExpression (ι:=ι) k)
  | 0,b,s,e,_ => [(b,s,e)]
  | j+1,b,s,e,t =>
      let P := pivotExpression k j e s t.1.1 t.1.2
      bottomExpressions k j b t.1.1 (childExpressions k j true e P) t.2.1 ++
        bottomExpressions k j (!b) t.1.2 (childExpressions k j false e P) t.2.2

def evalBottom (k:ℕ) (a:ι→ℤ) (z:BottomExpression (ι:=ι) k) : BottomDatum k :=
  (z.1,z.2.1,evalExpressions a z.2.2)

theorem bottomExpressions_eval (k j:ℕ) (b:Bool) (s:ℤ) (e:Expressions (ι:=ι) k j)
    (t:HistoryReconstruction.Tree j) (a:ι→ℤ) :
    (bottomExpressions k j b s e t).map (evalBottom k a)=
      bottomData k j b s (evalExpressions a e) t := by
  induction j generalizing b s with
  | zero => rfl
  | succ j ih => simp only [bottomExpressions,bottomData,List.map_append,ih,
      childExpressions_eval,pivotExpression_eval]

theorem bottomExpressions_length (k j:ℕ) (b:Bool) (s:ℤ) (e:Expressions (ι:=ι) k j)
    (t:HistoryReconstruction.Tree j) : (bottomExpressions k j b s e t).length=2^j := by
  induction j generalizing b s with
  | zero => rfl
  | succ j ih => simp only [bottomExpressions,List.length_append,ih,pow_succ]; omega

def periodExpression (k:ℕ) (e:Expressions (ι:=ι) k 0) : Expr ι := finiteProductExpression e

theorem periodExpression_eval (k:ℕ) (e:Expressions (ι:=ι) k 0) (a:ι→ℤ) :
    (periodExpression k e).integerEval a=period k 0 (evalExpressions a e) :=
  finiteProductExpression_eval _ _

theorem bottomExpressions_good (k:ℕ) (B V:(j:ℕ)→State k (j+1)→ℤ) (j:ℕ)
    (b:Bool) (s:ℤ) (e:Expressions (ι:=ι) k j) (t:HistoryReconstruction.Tree j) (a:ι→ℤ)
    (he:∀i,HistoryReconstruction.Good a (e i))
    (h:Supported k B V j s (evalExpressions a e) t) :
    ∀z∈bottomExpressions k j b s e t,∀i,HistoryReconstruction.Good a (z.2.2 i) := by
  induction j generalizing b s with
  | zero =>
    intro z hz
    have hz' : z=(b,s,e) := List.mem_singleton.mp hz
    subst z
    exact he
  | succ j ih =>
    let P := pivotExpression k j e s t.1.1 t.1.2
    have hP : HistoryReconstruction.Good a P := pivotExpression_good k j e _ _ _ _ _ a he h.1
    have hleft : Supported k B V j t.1.1
        (evalExpressions a (childExpressions k j true e P)) t.2.1 := by
      rw [childExpressions_eval,pivotExpression_eval]
      exact h.2.1
    have hright : Supported k B V j t.1.2
        (evalExpressions a (childExpressions k j false e P)) t.2.2 := by
      rw [childExpressions_eval,pivotExpression_eval]
      exact h.2.2
    intro z hz
    rcases List.mem_append.mp hz with hz|hz
    · exact ih b _ _ t.2.1 (childExpressions_preserves k j true e P _ he hP) hleft z hz
    · exact ih (!b) _ _ t.2.2 (childExpressions_preserves k j false e P _ he hP) hright z hz

theorem bottom_period_cleared (k:ℕ) (B V:(j:ℕ)→State k (j+1)→ℤ) (j:ℕ)
    (b:Bool) (s:ℤ) (e:Expressions (ι:=ι) k j) (t:HistoryReconstruction.Tree j) (a:ι→ℤ)
    (he:∀i,HistoryReconstruction.Good a (e i))
    (h:Supported k B V j s (evalExpressions a e) t)
    (z:BottomExpression (ι:=ι) k) (hz:z∈bottomExpressions k j b s e t) :
    (periodExpression k z.2.2).denominator≠0 ∧
      (periodExpression k z.2.2).denominator*period k 0 (evalExpressions a z.2.2)=
        MvPolynomial.eval a (periodExpression k z.2.2).numerator := by
  have hg := finiteProductExpression_good z.2.2 a
    (bottomExpressions_good k B V j b s e t a he h z hz)
  exact ⟨(periodExpression k z.2.2).denominator_ne_zero hg.1,
    (periodExpression_eval k z.2.2 a) ▸ (periodExpression k z.2.2).integerEval_cleared a hg.2⟩

theorem weight_eq_symbolic_profiles (k:ℕ) (mask:(j:ℕ)→ℤ→State k j→Prop)
    (X Δ W:ℝ) (hX:0<X) (j:ℕ) (b:Bool) (s:ℤ) (e:Expressions (ι:=ι) k j)
    (t:HistoryReconstruction.Tree j) (a:ι→ℤ)
    (h:WeightSupport k mask X Δ W j s (evalExpressions a e) t) :
    conjugateBy b (weight k mask X Δ W j s (evalExpressions a e) t)=
      ((bottomExpressions k j b s e t).map (fun z=>profileValue k X (evalBottom k a z))).prod := by
  rw [weight_eq_profile_product k mask X Δ W hX j b s (evalExpressions a e) t h,
    ← bottomExpressions_eval k j b s e t a,List.map_map]
  rfl

end Ostmann.Characters.Template

end

end OAI
