import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.Density

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E A : Type*} [Fintype E] [Fintype A]

lemma expect_eq_on (w v : E → A → ℝ) (hw : ∀ e, ∑ a, w e a = 1)
    (hv : ∀ e, ∑ a, v e a = 1) (S : Set E) (f : (E → A) → ℝ)
    (hf : DependsOn f S) (heq : ∀ e ∈ S, w e = v e) :
    expect w f = expect v f := by
  obtain ⟨f',rfl⟩ := dependsOn_iff_exists_comp.mp hf
  have restrict (u : E → A → ℝ) (hu : ∀ e, ∑ a, u e a = 1) :
      expect u (fun ω => f' (fun e => ω e)) = expect (fun e : S => u e) f' := by
    have h := expect_factor u (fun e => e ∈ S) f' (fun _ => 1)
    have hc : expect (fun e : {e // e ∉ S} => u e) (fun _ => 1) = 1 :=
      expect_const (fun e : {e // e ∉ S} => u e) (fun e => hu e) 1
    simpa only [mul_one,hc] using h
  change expect w (fun ω => f' (fun e => ω e)) = expect v (fun ω => f' (fun e => ω e))
  rw [restrict w hw,restrict v hv]
  congr 1
  funext e
  exact heq e e.property

noncomputable def exposureLaw (w : E → A → ℝ) (D : Set E) (σ : E → A)
    (e : E) (b : A) : ℝ := if e ∈ D then (if b = σ e then 1 else 0) else w e b

omit [Fintype E] in
lemma exposureLaw_normalized (w : E → A → ℝ) (D : Set E) (σ : E → A)
    (hw : ∀ e, ∑ b, w e b = 1) : ∀ e, ∑ b, exposureLaw w D σ e b = 1 := by
  intro e
  by_cases he : e ∈ D
  · simp [exposureLaw,he]
  · simpa only [exposureLaw,ite_eq_right he] using hw e

omit [Fintype E] [Fintype A] in
lemma exposureLaw_nonneg (w : E → A → ℝ) (D : Set E) (σ : E → A)
    (hn : ∀ e b, 0 ≤ w e b) : ∀ e b, 0 ≤ exposureLaw w D σ e b := by
  intro e b
  unfold exposureLaw
  split_ifs <;> first | positivity | exact hn e b

end CriticalPercolation.FiniteProduct

end
end

end OAI
