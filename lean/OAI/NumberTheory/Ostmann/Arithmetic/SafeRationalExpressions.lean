import OAI.NumberTheory.Ostmann.Arithmetic.HistorySymbolicStep
import OAI.NumberTheory.Ostmann.Arithmetic.MonomialDenominators

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.SafeRationalExpressions
open Characters.RationalHistory

variable {ι : Type*}

inductive Denominator (S : Set ℤ) : Expr ι → Prop
  | atom (i : ι) : Denominator S (.atom i)
  | one : Denominator S (.fixed 1)
  | frequency (s : ℤ) (hs : s ∈ S) : Denominator S (.fixed s)
  | mul {a b : Expr ι} : Denominator S a → Denominator S b → Denominator S (.mul a b)

inductive Expression (S : Set ℤ) : Expr ι → Prop
  | atom (i : ι) : Expression S (.atom i)
  | fixed (c : ℤ) : Expression S (.fixed c)
  | add {a b : Expr ι} : Expression S a → Expression S b → Expression S (.add a b)
  | sub {a b : Expr ι} : Expression S a → Expression S b → Expression S (.sub a b)
  | mul {a b : Expr ι} : Expression S a → Expression S b → Expression S (.mul a b)
  | divide {a b : Expr ι} : Expression S a → Denominator S b → Expression S (.divide a b)

theorem Denominator.expression {S : Set ℤ} {e : Expr ι} (he : Denominator S e) : Expression S e := by
  induction he with
  | atom i => exact .atom i
  | one => exact .fixed 1
  | frequency s hs => exact .fixed s
  | mul ha hb ia ib => exact .mul ia ib

theorem Denominator.product {S : Set ℤ} (es : List (Expr ι))
    (h : ∀ e ∈ es, Denominator S e) : Denominator S (HistorySymbolicStep.product es) := by
  induction es with
  | nil => exact .one
  | cons e es ih => exact .mul (h e (by simp)) (ih (fun z hz => h z (by simp [hz])))

theorem Denominator.product_ofFn {S : Set ℤ} {n : ℕ} (f : Fin n → Expr ι)
    (h : ∀ i, Denominator S (f i)) : Denominator S (HistorySymbolicStep.product (List.ofFn f)) := by
  apply Denominator.product
  intro e he
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
  exact h i

theorem Denominator.fieldRegular {S : Set ℤ} {e : Expr ι} (he : Denominator S e)
    {K : Type*} [Field K] (x : ι → K) : e.FieldRegularAt x := by
  induction he with
  | atom i | one | frequency s hs => trivial
  | mul ha hb ia ib => exact ⟨ia,ib⟩

theorem Denominator.fieldEval_ne_zero {S : Set ℤ} {e : Expr ι}
    (he : Denominator S e) {K : Type*} [Field K] [DecidableEq ι]
    (x : ι → K) (hS : ∀ s ∈ S, (s:K) ≠ 0)
    (hx : ∀ i ∈ e.atoms, x i ≠ 0) : e.fieldEval x ≠ 0 := by
  induction he with
  | atom i => exact hx i (by simp [Expr.atoms])
  | one => simp [Expr.fieldEval]
  | frequency s hs => exact hS s hs
  | @mul a b ha hb ia ib =>
      exact mul_ne_zero (ia (fun i hi => hx i (Finset.mem_union_left _ hi)))
        (ib (fun i hi => hx i (Finset.mem_union_right _ hi)))

theorem Expression.fieldRegular {S : Set ℤ} {e : Expr ι}
    (he : Expression S e) {K : Type*} [Field K] [DecidableEq ι]
    (x : ι → K) (hS : ∀ s ∈ S, (s:K) ≠ 0)
    (hx : ∀ i ∈ e.atoms, x i ≠ 0) : e.FieldRegularAt x := by
  induction he with
  | atom i | fixed c => trivial
  | @add a b ha hb ia ib | @sub a b ha hb ia ib | @mul a b ha hb ia ib =>
      exact ⟨ia (fun i hi => hx i (Finset.mem_union_left _ hi)),
        ib (fun i hi => hx i (Finset.mem_union_right _ hi))⟩
  | @divide a b ha hb ia =>
      exact ⟨ia (fun i hi => hx i (Finset.mem_union_left _ hi)),
        hb.fieldRegular x,hb.fieldEval_ne_zero x hS (fun i hi => hx i (Finset.mem_union_right _ hi))⟩

theorem Denominator.generated {S : Set ℤ} {e : Expr ι} (he : Denominator S e) :
    MonomialDenominators.Generated S e.numerator ∧
      MonomialDenominators.Generated S e.denominator := by
  induction he with
  | atom i => exact ⟨.var i,.one⟩
  | one => exact ⟨by simpa [Expr.numerator,Expr.fraction] using (MonomialDenominators.Generated.one (S:=S) (ι:=ι)),.one⟩
  | frequency s hs => exact ⟨.constant s hs,.one⟩
  | mul ha hb ia ib => exact ⟨.mul ia.1 ib.1,.mul ia.2 ib.2⟩

theorem Expression.denominator_generated {S : Set ℤ} {e : Expr ι} (he : Expression S e) :
    MonomialDenominators.Generated S e.denominator := by
  induction he with
  | atom i | fixed c => exact .one
  | add ha hb ia ib | sub ha hb ia ib | mul ha hb ia ib => exact .mul ia ib
  | divide ha hb ia => exact .mul ia hb.generated.1

end Ostmann.Arithmetic.SafeRationalExpressions

end

end OAI
