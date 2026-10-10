import OAI.MeasureTheory.Falconer.Geometry.ScalarDyadicGrid

namespace OAI

/-! An actual coefficient from the dyadic grid gives a large scalar
projection. All constants come from the finite collision estimate. -/
namespace Falconer
open scoped Pointwise

theorem dense_projection_obstruction_divide {δ A N M B : ℝ}
    (hδ : 0 < δ) (hM : 0 ≤ M) (hB : 0 ≤ B) (hA : 1 ≤ δ*A)
    (hbound : A*N^2 ≤ M*(A+B*N^2)) :
    N^2/(1+B*δ*N^2) ≤ M := by
  have hA0 : 0 < A := by nlinarith
  have hden : 0 < 1+B*δ*N^2 := by positivity
  have ht := mul_le_mul_of_nonneg_right hA (mul_nonneg hB (sq_nonneg N))
  have hpad : A+B*N^2 ≤ A*(1+B*δ*N^2) := by nlinarith
  have hh := hbound.trans (mul_le_mul_of_nonneg_left hpad hM)
  apply (div_le_iff₀ hden).2
  apply (mul_le_mul_iff_right₀ hA0).1
  nlinarith

theorem scalar_grid_large_projection (n : ℕ) {K κ : ℝ}
    (hK : 0 ≤ K) (hκ : 0 < κ) (hκ1 : κ ≤ 1/2)
    (X : Finset ℝ) (hX : X.Nonempty)
    (hsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → 1/(2:ℝ)^n ≤ |x-y|)
    (hball : ∀ u r : ℝ, 1/(2:ℝ)^n ≤ r → r ≤ 1 →
      ((X.filter fun x => |x-u| ≤ r).card : ℝ) ≤ K*r^κ*(X.card : ℝ)) :
    let δ : ℝ := 1/(2:ℝ)^n
    let θ := productInterpolationWeight κ
    let C := max 1 (81^θ*K^(2*(1-θ))*(δ*(X.card : ℝ))^(-(2*θ)))
    ∃ c ∈ scalarDyadicGrid n,
      (X.card : ℝ)^2/(1+(5+12*C*planarPotentialConstant 1 (1+κ/2))*δ*(X.card : ℝ)^2) ≤
        ((scalarCells δ (X+X.image (fun x => c*x))).card : ℝ) := by
  classical
  dsimp only
  let δ : ℝ := 1/(2:ℝ)^n
  let θ := productInterpolationWeight κ
  let C := max 1 (81^θ*K^(2*(1-θ))*(δ*(X.card : ℝ))^(-(2*θ)))
  let f := fun c => (scalarCells δ (X+X.image (fun x => c*x))).card
  obtain ⟨c,hc,hmax⟩ := (scalarDyadicGrid n).exists_max_image f (scalarDyadicGrid_nonempty n)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hproj (b : ℝ) (hb : b ∈ scalarDyadicGrid n) :
      ((scalarCells δ (X+X.image (fun x => b*x))).card : ℝ) ≤ (f c : ℝ) := by
    exact_mod_cast hmax b hb
  have hh := scalar_dyadic_uniform_projection n hK hκ hκ1 hδ (Nat.cast_nonneg (f c))
    (scalarDyadicGrid n) X hX (scalarDyadicGrid_bound n) (scalarDyadicGrid_separated n) hsep hball hproj
  have hB : 0 ≤ 5+12*C*planarPotentialConstant 1 (1+κ/2) := by
    have hp := planarPotentialConstant_pos (show (1 : ℝ) < 1+κ/2 by linarith)
    have hC : 0 ≤ C := (show (0 : ℝ) ≤ 1 by norm_num).trans (le_max_left _ _)
    positivity
  have hh' : ((scalarDyadicGrid n).card : ℝ)*(X.card : ℝ)^2 ≤
      (f c : ℝ)*(((scalarDyadicGrid n).card : ℝ)+
        (5+12*C*planarPotentialConstant 1 (1+κ/2))*(X.card : ℝ)^2) := by
    change ((scalarDyadicGrid n).card : ℝ)*(X.card : ℝ)^2 ≤
      (f c : ℝ)*(((scalarDyadicGrid n).card : ℝ)+
        (5+12*(δ/δ)*C*planarPotentialConstant 1 (1+κ/2))*(X.card : ℝ)^2) at hh
    simpa only [div_self hδ.ne',mul_one] using hh
  refine ⟨c,hc,?_⟩
  exact dense_projection_obstruction_divide hδ (Nat.cast_nonneg (f c)) hB
    (scalarDyadicGrid_density n) hh'

end Falconer

end OAI
