import OAI.MeasureTheory.Falconer.Geometry.ScalarClosureProjections
import OAI.MeasureTheory.Falconer.Geometry.ScalarGridProjection

namespace OAI

/-! The projection obstruction once a finite coefficient closure covers
an actual grid, under the covering hypothesis for the coefficient closure. -/
namespace Falconer
open scoped Pointwise

 theorem scalar_generated_grid_obstruction (n k M : ℕ) {K F κ : ℝ}
    (hK : 1 ≤ K) (hF : 0 ≤ F) (hκ : 0 < κ) (hκ1 : κ ≤ 1/2)
    (X S : Finset ℝ) (hX : X.Nonempty)
    (hXbound : ∀ x ∈ X, |x| ≤ 1)
    (hS : ∀ a ∈ S, |a| ≤ M)
    (hsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → 1/(2:ℝ)^n ≤ |x-y|)
    (hball : ∀ u r : ℝ, 1/(2:ℝ)^n ≤ r → r ≤ 1 →
      ((X.filter fun x => |x-u| ≤ r).card : ℝ) ≤ F*r^κ*(X.card : ℝ))
    (hdoubling : ((scalarCells (1/(2:ℝ)^n) (X+X)).card : ℝ) ≤
      K*(scalarCells (1/(2:ℝ)^n) X).card)
    (hproj : ∀ a ∈ S,
      ((scalarCells (1/(2:ℝ)^n) (X+X.image (fun x => a*x))).card : ℝ) ≤
        K*(scalarCells (1/(2:ℝ)^n) X).card)
    (hcover : ∀ c ∈ scalarDyadicGrid n, ∃ a ∈ scalarCoefficientClosure S k,
      |c-a| ≤ 2*(1/(2:ℝ)^n)) :
    let δ : ℝ := 1/(2:ℝ)^n
    let θ := productInterpolationWeight κ
    let C := max 1 (81^θ*F^(2*(1-θ))*(δ*(X.card : ℝ))^(-(2*θ)))
    (X.card : ℝ)^2/(1+(5+12*C*planarPotentialConstant 1 (1+κ/2))*δ*(X.card : ℝ)^2) ≤
      7*scalarCoefficientBudget M K k*(X.card : ℝ) := by
  dsimp only
  have hδ : 0 < 1/(2:ℝ)^n := by positivity
  have hcell : (scalarCells (1/(2:ℝ)^n) X).card = X.card :=
    Finset.card_image_of_injOn (scalarCells_injective hδ hsep)
  obtain ⟨c,hc,hlarge⟩ := scalar_grid_large_projection n hF hκ hκ1 X hX hsep hball
  obtain ⟨a,ha,hca⟩ := hcover c hc
  have hnear : ((scalarCells (1/(2:ℝ)^n) (X+X.image (fun x => c*x))).card : ℝ) ≤
      7*((scalarCells (1/(2:ℝ)^n) (X+X.image (fun x => a*x))).card : ℝ) := by
    exact_mod_cast scalar_linear_sum_stability hδ X X hXbound (by simpa only [mul_one] using hca)
  have hsmall := scalar_closure_projections hδ hK X S hX M hS hdoubling hproj k a ha
  rw [hcell] at hsmall
  exact hlarge.trans (hnear.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsmall (show (0 : ℝ) ≤ 7 by norm_num)))

end Falconer

end OAI
