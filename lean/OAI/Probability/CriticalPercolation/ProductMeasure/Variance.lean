import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.Delta
import OAI.Probability.CriticalPercolation.ProductMeasure.ProbRequiresBit

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

lemma prob_true (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1) :
    prob w (fun _ => True) = 1 := by
  simpa only [prob, ite_true] using expect_const w hw 1

lemma prob_le_one (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hn : ∀ e b, 0 ≤ w e b) (F : Set E → Prop) : prob w F ≤ 1 := by
  exact (prob_mono w hn (fun _ _ => True.intro)).trans_eq (prob_true w hw)

lemma delta_unit (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hn : ∀ e b, 0 ≤ w e b) (e : E) (h0 : w e False ≠ 0) (h1 : w e True ≠ 0)
    (F : Set E → Prop) (hF : ∀ s t, s ⊆ t → F s → F t) :
    0 ≤ delta w F e ∧ delta w F e ≤ 1 := by
  rw [delta_eq_pivotal w hw e h0 h1 F hF]
  exact ⟨prob_nonneg _ (pin_nonneg w hn e False) _,
    prob_le_one _ (pin_normalized w hw e False) (pin_nonneg w hn e False) _⟩

lemma prob_openPivot_pin (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (e : E) (h0 : w e False ≠ 0) (h1 : w e True ≠ 0)
    (F : Set E → Prop) (hF : ∀ s t, s ⊆ t → F s → F t) :
    prob (pin w e True) (openPivot F e) = delta w F e := by
  rw [prob_pin_transport w hw e False True h0 h1,
    delta_eq_pivotal w hw e h0 h1 F hF]
  apply prob_congr_support
  intro ω hω
  erw [openPivot_force_true]
  have hh := density_pin_support w e False ω hω
  have heq : Function.update ω e False = ω := by
    erw [← hh,Function.update_eq_self]
  erw [heq]

lemma prob_openPivot (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (e : E) (h0 : w e False ≠ 0) (h1 : w e True ≠ 0)
    (F : Set E → Prop) (hF : ∀ s t, s ⊆ t → F s → F t) :
    prob w (openPivot F e) = w e True * delta w F e := by
  rw [prob_requires_bit w e True _ (fun _ h => propext (iff_true_intro h.1)),
    prob_openPivot_pin w hw e h0 h1 F hF]

noncomputable def variance (w : E → Prop → ℝ) (F : Set E → Prop) : ℝ :=
  prob w F - (prob w F)^2

lemma variance_eq_potential (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (F : Set E → Prop) : variance w F = potential w (fun _ => True) F := by
  simp only [variance,potential,prob_true w hw,div_one]

lemma variance_nonneg (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hn : ∀ e b, 0 ≤ w e b) (F : Set E → Prop) : 0 ≤ variance w F := by
  rw [variance_eq_potential w hw]
  exact potential_nonneg w hn _ _ (fun _ _ => trivial)

lemma variance_le_one (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hn : ∀ e b, 0 ≤ w e b) (F : Set E → Prop) : variance w F ≤ 1 := by
  exact (sub_le_self _ (sq_nonneg _)).trans (prob_le_one w hw hn F)

lemma variance_split (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hn : ∀ e b, 0 ≤ w e b) (F : Set E → Prop) (e : E)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (h0 : w e False = 1-p) (h1 : w e True = p) :
    variance w F = p*(1-p)*(delta w F e)^2 +
      (1-p)*variance (pin w e False) F + p*variance (pin w e True) F := by
  have hh := potential_split w hn e (fun _ => True) F (fun _ _ => trivial) hp.1 hp.2 h0 h1
  simp only [prob_true _ (pin_normalized w hw e False),
    prob_true _ (pin_normalized w hw e True),mul_one,div_one,sub_add_cancel,div_one,
    ← variance_eq_potential w hw,
    ← variance_eq_potential _ (pin_normalized w hw e False),
    ← variance_eq_potential _ (pin_normalized w hw e True)] at hh
  dsimp only [delta]
  linarith

end CriticalPercolation.FiniteProduct

end
end

end OAI
