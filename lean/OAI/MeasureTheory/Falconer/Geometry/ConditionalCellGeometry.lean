import OAI.MeasureTheory.Falconer.Measures.OriginalConditionalFrostman

namespace OAI

/-! # Original conditional laws stay within the actual dyadic cell diameter -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem conditional_cell_pair_geometry (Q : DyadicCube d) (hQ : Q.side = 1)
    (ρ : Measure (Space d)) (P : CellPath d) {g : ℕ} (hP : P.length = g)
    {D : ℝ} (hD : Real.sqrt d ≤ D)
    (G : Set (Space d × Space d))
    (hpin : ∀ z x, (z,x) ∈ G → ∀ y ∈ (Q.descendant P).carrier, ‖y-x‖ ≤ D) :
    ∀ᵐ z ∂ProbabilityTheory.cond ρ (Q.descendant P).carrier,
      ∀ᵐ y ∂ProbabilityTheory.cond ρ (Q.descendant P).carrier,
        ‖y-z‖ ≤ D/(2:ℝ)^g ∧ ∀ x, (z,x) ∈ G → ‖y-x‖ ≤ D := by
  apply ProbabilityTheory.ae_cond_of_forall_mem (Q.descendant P).measurable
  intro z hz
  apply ProbabilityTheory.ae_cond_of_forall_mem (Q.descendant P).measurable
  intro y hy
  refine ⟨?_,fun x hx => hpin z x hx y hy⟩
  have hside : 0 ≤ (Q.descendant P).side := by rw [Q.descendant_side,hQ]; positivity
  have hh := (Q.descendant P).dist_le hside hy hz
  rw [dist_eq_norm,Q.descendant_side,hQ,hP] at hh
  apply hh.trans
  simpa only [mul_one_div] using div_le_div_of_nonneg_right hD
    (by positivity : (0:ℝ) ≤ 2^g)

end Falconer.Regularization

end OAI
