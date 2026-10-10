import OAI.NumberTheory.Ostmann.Arithmetic.HistoryLinearization
import OAI.NumberTheory.Ostmann.Characters.RationalHistoryDegree

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySymbolicStep
open Construction Characters.RationalHistory

variable {ι : Type*}

def product : List (Expr ι) → Expr ι
  | [] => .fixed 1
  | e::es => .mul e (product es)

theorem product_eval (es : List (Expr ι)) (x : ι → ℚ) :
    (product es).rationalEval x = (es.map (fun e => e.rationalEval x)).prod := by
  induction es with
  | nil => simp [product,Expr.rationalEval]
  | cons e es ih => simp [product,Expr.rationalEval,ih]

theorem product_regular (es : List (Expr ι)) (x : ι → ℚ)
    (h : ∀ e ∈ es, e.RegularAt x) : (product es).RegularAt x := by
  induction es with
  | nil => trivial
  | cons e es ih => exact ⟨h e (by simp),ih (fun z hz => h z (by simp [hz]))⟩

theorem product_atomCount (es : List (Expr ι)) :
    (product es).atomCount = (es.map Expr.atomCount).sum := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [product,Expr.atomCount,ih]

def pivot (s v w : ℤ) (plus minus : Expr ι) (u hp hm : List (Expr ι)) : Expr ι :=
  .divide (.sub (.mul (.fixed v) (.mul minus (product hm)))
    (.mul (.fixed w) (.mul plus (product hp)))) (.mul (.fixed s) (product u))

theorem pivot_eval (s v w : ℤ) (plus minus : Expr ι) (u hp hm : List (Expr ι))
    (x : ι → ℚ) :
    (pivot s v w plus minus u hp hm).rationalEval x =
      ((v:ℚ)*(minus.rationalEval x*(product hm).rationalEval x) -
        (w:ℚ)*(plus.rationalEval x*(product hp).rationalEval x)) /
      ((s:ℚ)*(product u).rationalEval x) := rfl

theorem supported_pivot_eval {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (plus minus : Expr ι) (ue hpe hme : List (Expr ι)) (x : ι → ℚ)
    (heplus : plus.rationalEval x = (a.giantPlus:ℚ))
    (heminus : minus.rationalEval x = (a.giantMinus:ℚ))
    (heu : (product ue).rationalEval x = ((u.map SmallSlot.value).prod:ℚ))
    (hehp : (product hpe).rationalEval x = ((hp.map SmallSlot.value).prod:ℚ))
    (hehm : (product hme).rationalEval x = ((hm.map SmallSlot.value).prod:ℚ)) :
    (pivot a.frequency left.root.frequency right.root.frequency plus minus ue hpe hme).rationalEval x = (p:ℚ) := by
  rw [pivot_eval,heplus,heminus,heu,hehp,hehm]
  have hs0 : (a.frequency:ℚ) ≠ 0 := by
    exact_mod_cast History.supported_root_frequency_ne_zero hs
  have hu0 : ((u.map SmallSlot.value).prod:ℚ) ≠ 0 := by
    exact_mod_cast (History.supported_compensation_product_pos hs).ne'
  apply (div_eq_iff (mul_ne_zero hs0 hu0)).mpr
  have hc := congrArg (fun z : ℤ => (z:ℚ)) (History.supported_reversal hs)
  simp only [reversalNumerator,Int.cast_sub,Int.cast_mul,Int.cast_natCast,Nat.cast_mul] at hc
  simpa only [mul_comm (p:ℚ)] using hc

theorem supported_pivot_regular {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (plus minus : Expr ι) (ue hpe hme : List (Expr ι)) (x : ι → ℚ)
    (hrplus : plus.RegularAt x) (hrminus : minus.RegularAt x)
    (hru : (product ue).RegularAt x) (hrhp : (product hpe).RegularAt x)
    (hrhm : (product hme).RegularAt x)
    (heu : (product ue).rationalEval x = ((u.map SmallSlot.value).prod:ℚ)) :
    (pivot a.frequency left.root.frequency right.root.frequency plus minus ue hpe hme).RegularAt x := by
  have hs0 : (a.frequency:ℚ) ≠ 0 := by
    exact_mod_cast History.supported_root_frequency_ne_zero hs
  have hu0 : ((u.map SmallSlot.value).prod:ℚ) ≠ 0 := by
    exact_mod_cast (History.supported_compensation_product_pos hs).ne'
  refine ⟨⟨⟨trivial,hrminus,hrhm⟩,⟨trivial,hrplus,hrhp⟩⟩,⟨trivial,hru⟩,?_⟩
  change (a.frequency:ℚ)*(product ue).rationalEval x ≠ 0
  rw [heu]
  exact mul_ne_zero hs0 hu0

theorem pivot_atomCount (s v w : ℤ) (plus minus : Expr ι) (u hp hm : List (Expr ι)) :
    (pivot s v w plus minus u hp hm).atomCount = plus.atomCount + minus.atomCount +
      (u.map Expr.atomCount).sum + (hp.map Expr.atomCount).sum + (hm.map Expr.atomCount).sum := by
  simp only [pivot,Expr.atomCount,product_atomCount]
  omega

end Ostmann.Arithmetic.HistorySymbolicStep

end

end OAI
