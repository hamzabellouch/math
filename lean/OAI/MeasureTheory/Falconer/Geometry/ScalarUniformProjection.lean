import OAI.MeasureTheory.Falconer.Geometry.ScalarKernelGeometry
import OAI.MeasureTheory.Falconer.Recursion.ScalarProductPotential
import OAI.MeasureTheory.Falconer.Geometry.ScalarProjectionComparison

namespace OAI

/-! A quantitative obstruction to uniformly small projections for a
separated family of scalar coefficients. -/
namespace Falconer
open scoped Pointwise

theorem scalar_projection_from_potential {δ η M V : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hM : 0 ≤ M)
    (A X : Finset ℝ) (hX : X.Nonempty) (hA : ∀ c ∈ A, |c| ≤ 1)
    (hsepA : ∀ c ∈ A, ∀ d ∈ A, c ≠ d → η ≤ |c-d|)
    (hsepX : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ |x-y|)
    (hproj : ∀ c ∈ A, ((scalarCells δ (X+X.image (fun y => c*y))).card : ℝ) ≤ M)
    (hpot : ∀ z ∈ scalarProductPoints X X,
      (∑ q ∈ scalarProductPoints X X, 1/max (dist z q) δ) ≤ V) :
    (A.card : ℝ)*(X.card : ℝ)^2 ≤
      M*((A.card : ℝ)+5*(X.card : ℝ)^2+12*(δ/η)*V) := by
  have hlower := scalar_product_projection_comparison hδ hη hM A X X hA hsepA hsepX hproj
  have hupper := scalar_kernel_sum_le_potential hδ hη X X hsepX hpot
  have hh := hlower.trans (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl hupper) hM)
  have hN : 0 < (X.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hX)
  have hscaled : ((A.card : ℝ)*(X.card : ℝ)^2)*(X.card : ℝ)^2 ≤
      (M*((A.card : ℝ)+5*(X.card : ℝ)^2+12*(δ/η)*V))*(X.card : ℝ)^2 := by
    convert hh using 1 <;> ring
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos hN)).1 hscaled

theorem scalar_dyadic_uniform_projection (n : ℕ) {K κ η M : ℝ}
    (hK : 0 ≤ K) (hκ : 0 < κ) (hκ1 : κ ≤ 1/2) (hη : 0 < η) (hM : 0 ≤ M)
    (A X : Finset ℝ) (hX : X.Nonempty) (hA : ∀ c ∈ A, |c| ≤ 1)
    (hsepA : ∀ c ∈ A, ∀ d ∈ A, c ≠ d → η ≤ |c-d|)
    (hsepX : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → 1/(2:ℝ)^n ≤ |x-y|)
    (hball : ∀ u r : ℝ, 1/(2:ℝ)^n ≤ r → r ≤ 1 →
      ((X.filter fun x => |x-u| ≤ r).card : ℝ) ≤ K*r^κ*(X.card : ℝ))
    (hproj : ∀ c ∈ A,
      ((scalarCells (1/(2:ℝ)^n) (X+X.image (fun y => c*y))).card : ℝ) ≤ M) :
    let δ : ℝ := 1/(2:ℝ)^n
    let θ := productInterpolationWeight κ
    let C := max 1 (81^θ*K^(2*(1-θ))*(δ*(X.card : ℝ))^(-(2*θ)))
    (A.card : ℝ)*(X.card : ℝ)^2 ≤
      M*((A.card : ℝ)+(5+12*(δ/η)*C*planarPotentialConstant 1 (1+κ/2))*(X.card : ℝ)^2) := by
  dsimp only
  let δ : ℝ := 1/(2:ℝ)^n
  let θ := productInterpolationWeight κ
  let C := max 1 (81^θ*K^(2*(1-θ))*(δ*(X.card : ℝ))^(-(2*θ)))
  let V := C*planarPotentialConstant 1 (1+κ/2)*(X.card : ℝ)^2
  have hp : ∀ z ∈ scalarProductPoints X X,
      (∑ q ∈ scalarProductPoints X X, 1/max (dist z q) δ) ≤ V := by
    intro z _
    exact scalar_product_dyadic_potential n hK hκ hκ1 X hX hsepX hball z
  have hh := scalar_projection_from_potential (by positivity) hη hM
    A X hX hA hsepA hsepX hproj hp
  change (A.card : ℝ)*(X.card : ℝ)^2 ≤
    M*((A.card : ℝ)+5*(X.card : ℝ)^2+
      12*(δ/η)*(C*planarPotentialConstant 1 (1+κ/2)*(X.card : ℝ)^2)) at hh
  change (A.card : ℝ)*(X.card : ℝ)^2 ≤
    M*((A.card : ℝ)+(5+12*(δ/η)*C*planarPotentialConstant 1 (1+κ/2))*(X.card : ℝ)^2)
  convert hh using 1
  ring

end Falconer

end OAI
