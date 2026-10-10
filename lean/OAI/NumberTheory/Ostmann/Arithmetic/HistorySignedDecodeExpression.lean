import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedDecodeIntegral
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightRegular

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedDecode
open Construction Characters.RationalHistory HistorySymbolicStep
variable {ι : Type*}

theorem pivot_realEval_eq_signedPivot (a : SignedState) (v w : ℤ)
    (u hp hm : List SmallSlot)
    (hden : a.frequency * ((u.map SmallSlot.value).prod : ℤ) ≠ 0)
    (hd : a.frequency * ((u.map SmallSlot.value).prod : ℤ) ∣
      reversalNumerator v w (a.giantPlus * ((hp.map SmallSlot.value).prod : ℤ))
        (a.giantMinus * ((hm.map SmallSlot.value).prod : ℤ)))
    (plus minus : Expr ι) (ue hpe hme : List (Expr ι)) (x : ι → ℝ)
    (heplus : plus.realEval x = (a.giantPlus : ℝ))
    (heminus : minus.realEval x = (a.giantMinus : ℝ))
    (heu : (product ue).realEval x = ((u.map SmallSlot.value).prod : ℝ))
    (hehp : (product hpe).realEval x = ((hp.map SmallSlot.value).prod : ℝ))
    (hehm : (product hme).realEval x = ((hm.map SmallSlot.value).prod : ℝ)) :
    (pivot a.frequency v w plus minus ue hpe hme).realEval x =
      (signedPivot a v w u hp hm : ℝ) := by
  rw [pivot_realEval, heplus, heminus, heu, hehp, hehm,
    signedPivot_real_eq a v w u hp hm hden hd]
  ring

theorem pivot_realRegular_of_signed_denominator (a : SignedState) (v w : ℤ)
    (u : List SmallSlot)
    (hden : a.frequency * ((u.map SmallSlot.value).prod : ℤ) ≠ 0)
    (plus minus : Expr ι) (ue hpe hme : List (Expr ι)) (x : ι → ℝ)
    (hrplus : plus.RealRegularAt x) (hrminus : minus.RealRegularAt x)
    (hru : (product ue).RealRegularAt x) (hrhp : (product hpe).RealRegularAt x)
    (hrhm : (product hme).RealRegularAt x)
    (heu : (product ue).realEval x = ((u.map SmallSlot.value).prod : ℝ)) :
    (pivot a.frequency v w plus minus ue hpe hme).RealRegularAt x := by
  refine ⟨⟨⟨trivial, hrminus, hrhm⟩, ⟨trivial, hrplus, hrhp⟩⟩,
    ⟨trivial, hru⟩, ?_⟩
  change (a.frequency : ℝ) * (product ue).realEval x ≠ 0
  rw [heu]
  have hs : (a.frequency : ℝ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero_iff.mp hden).1
  have hu : ((u.map SmallSlot.value).prod : ℝ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero_iff.mp hden).2
  exact mul_ne_zero hs hu

theorem pivot_realRegular_of_signed_entries (a : SignedState) (v w : ℤ)
    (u : List SmallSlot)
    (hden : a.frequency * ((u.map SmallSlot.value).prod : ℤ) ≠ 0)
    (plus minus : Expr ι) (ue hpe hme : List (Expr ι)) (x : ι → ℝ)
    (hrplus : plus.RealRegularAt x) (hrminus : minus.RealRegularAt x)
    (hru : ∀ e ∈ ue, e.RealRegularAt x)
    (hrhp : ∀ e ∈ hpe, e.RealRegularAt x)
    (hrhm : ∀ e ∈ hme, e.RealRegularAt x)
    (heu : (product ue).realEval x = ((u.map SmallSlot.value).prod : ℝ)) :
    (pivot a.frequency v w plus minus ue hpe hme).RealRegularAt x :=
  pivot_realRegular_of_signed_denominator a v w u hden plus minus ue hpe hme x
    hrplus hrminus (HistorySymbolicState.product_realRegular ue x hru)
    (HistorySymbolicState.product_realRegular hpe x hrhp)
    (HistorySymbolicState.product_realRegular hme x hrhm) heu

end Ostmann.Arithmetic.HistorySignedDecode

end

end OAI
