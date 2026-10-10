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

lemma coordinate_ne_zero_of_density (w : E → Prop → ℝ) (ω : Set E)
    (h : density w ω ≠ 0) (e : E) : w e (ω e) ≠ 0 := by
  exact (Finset.prod_ne_zero_iff.mp h) e (Finset.mem_univ e)

lemma density_force_nonzero (w : E → Prop → ℝ) (ω : Set E) (e : E) (b : Prop)
    (h : density w ω ≠ 0) (hb : w e b ≠ 0) :
    density w (Function.update ω e b) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  by_cases hj : j = e
  · subst j
    erw [Function.update_self]
    exact hb
  · erw [Function.update_of_ne hj]
    exact coordinate_ne_zero_of_density w ω h j

lemma density_pin_of_support (w : E → Prop → ℝ) (ω : Set E) (e : E) (b : Prop)
    (h : density w ω ≠ 0) (hb : ω e = b) : density (pin w e b) ω ≠ 0 := by
  erw [density_pin, ite_eq_left hb, one_mul]
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  exact coordinate_ne_zero_of_density w ω h j

lemma delta_congr_support (w : E → Prop → ℝ) (e : E)
    (h0 : w e False ≠ 0) (h1 : w e True ≠ 0) (F F' : Set E → Prop)
    (hF : ∀ ω, density w ω ≠ 0 → (F ω ↔ F' ω)) : delta w F e = delta w F' e := by
  unfold delta
  congr 1
  · exact prob_congr_support _ _ _ (fun ω hω => hF ω (density_pin_old_support w e True ω h1 hω))
  · exact prob_congr_support _ _ _ (fun ω hω => hF ω (density_pin_old_support w e False ω h0 hω))

lemma openPivot_congr_support (w : E → Prop → ℝ) (e : E) (h0 : w e False ≠ 0)
    (F F' : Set E → Prop) (hF : ∀ ω, density w ω ≠ 0 → (F ω ↔ F' ω))
    (ω : Set E) (hω : density w ω ≠ 0) : openPivot F e ω ↔ openPivot F' e ω := by
  unfold openPivot
  erw [hF ω hω,hF _ (density_force_nonzero w ω e False hω h0)]

end CriticalPercolation.FiniteProduct

end
end

end OAI
