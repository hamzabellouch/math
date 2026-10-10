import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.Delta

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E : Type*} [Fintype E]

lemma expect_closed_flip (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (e : E) {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (h0 : w e False = 1-p) (h1 : w e True = p) (f : Set E → ℝ) :
    expect w (fun ω => if ¬ω e then p*f (Function.update ω e True) else 0) =
      expect w (fun ω => if ω e then (1-p)*f ω else 0) := by
  have he0 : w e False ≠ 0 := by rw [h0]; linarith [hp.2]
  have he1 : w e True ≠ 0 := by rw [h1]; exact hp.1.ne'
  have he := expect_pin_transport w hw e False True he0 he1 f
  have hc : expect w (fun ω => if ¬ω e then p*f (Function.update ω e True) else 0) =
      w e False * expect (pin w e False) (fun ω => p*f (Function.update ω e True)) := by
    convert expect_prop_mask_pin w e False (fun ω => p*f (Function.update ω e True)) using 1
    congr 1
    funext ω
    by_cases hb : ω e <;> simp [hb]
  have ho : expect w (fun ω => if ω e then (1-p)*f ω else 0) =
      w e True * expect (pin w e True) (fun ω => (1-p)*f ω) := by
    convert expect_prop_mask_pin w e True (fun ω => (1-p)*f ω) using 1
    congr 1
    funext ω
    by_cases hb : ω e <;> simp [hb]
  erw [hc,ho,expect_const_mul,expect_const_mul,h0,h1,he]
  ring

lemma expect_closed_flip_decidable [d : DecidableEq E]
    (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (e : E) {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (h0 : w e False = 1-p) (h1 : w e True = p) (f : Set E → ℝ) :
    expect w (fun ω => if ¬ω e then p*f (Function.update ω e True) else 0) =
      expect w (fun ω => if ω e then (1-p)*f ω else 0) := by
  have hup (ω : Set E) :
      @Function.update E (fun _ => Prop) (fun a b => Classical.propDecidable (a=b)) ω e True =
        Function.update ω e True := by
    have hd : (fun a b => Classical.propDecidable (a=b)) = d := Subsingleton.elim _ _
    exact congrArg (fun d' : DecidableEq E =>
      @Function.update E (fun _ => Prop) d' ω e True) hd
  have h := expect_closed_flip w hw e hp h0 h1 f
  convert h using 1
  congr 1
  funext ω
  by_cases hc : ω e
  · simp only [hc,not_true_eq_false,ite_false]
  · simp only [hc,not_false_eq_true,ite_true]
    exact congrArg (fun σ : Set E => p*f σ) (hup ω).symm

end CriticalPercolation.FiniteProduct

end
end

end OAI
