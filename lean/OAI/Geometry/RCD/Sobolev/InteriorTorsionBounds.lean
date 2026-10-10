import OAI.Geometry.RCD.Sobolev.InteriorTorsionLaplacian

namespace OAI

/-! # The boundary error in the compact torsion test costs one inverse scale -/

open Set Metric MeasureTheory Laplacian
noncomputable section
namespace RegularPointCoordinates

theorem euclideanInteriorTorsion_laplacian_core {n : ℕ} (R : ℝ) {δ : ℝ} (hδ : 0<δ)
    {x : Euclidean n} (hx : 3*δ<euclideanQuadraticDefect n R x) :
    (Δ (euclideanInteriorTorsion n R δ)) x= -2*(n:ℝ) := by
  have hq : 2<euclideanQuadraticDefect n R x/δ := (lt_div_iff₀ hδ).mpr (by linarith)
  rw [euclideanInteriorTorsion_laplacian R hδ,
    boundaryTorsionProfile_second_zero (Or.inr hq),boundaryTorsionProfile_deriv_one hq]
  ring

theorem euclideanInteriorTorsion_laplacian_outside {n : ℕ} {R δ : ℝ} (hR : 0<R) (hδ : 0<δ)
    {x : Euclidean n} (hx : R≤‖x‖) : (Δ (euclideanInteriorTorsion n R δ)) x=0 := by
  have hq : euclideanQuadraticDefect n R x/δ<1 := (div_lt_one hδ).mpr (by
    dsimp only [euclideanQuadraticDefect]
    nlinarith [(sq_le_sq₀ hR.le (norm_nonneg x)).mpr hx])
  rw [euclideanInteriorTorsion_laplacian R hδ,boundaryTorsionProfile_second_zero (Or.inl hq),
    boundaryTorsionProfile_deriv_zero hq]
  ring

theorem euclideanInteriorTorsion_laplacian_upper (n : ℕ) {R : ℝ} (hR : 0<R) :
    ∃ A : ℝ, 0<A ∧ ∀ δ : ℝ, 0<δ → δ≤1 → ∀ x : Euclidean n,
      (Δ (euclideanInteriorTorsion n R δ)) x≤A/δ := by
  obtain ⟨C,hC,hb⟩ := boundaryTorsionProfile_two_derivative_bounds
  refine ⟨4*C*R^2+2*(n:ℝ)*C+1,by positivity,?_⟩
  intro δ hδ hδ1 x
  by_cases hx : R≤‖x‖
  · rw [euclideanInteriorTorsion_laplacian_outside hR hδ hx]
    positivity
  have hnx : ‖x‖≤R := (lt_of_not_ge hx).le
  have hxs : ‖x‖^2≤R^2 := (sq_le_sq₀ (norm_nonneg x) hR.le).mpr hnx
  let q := euclideanQuadraticDefect n R x/δ
  have hb₁ := (neg_le_abs (deriv boundaryTorsionProfile q)).trans (hb q).1
  have hb₂ := (le_abs_self (deriv (deriv boundaryTorsionProfile) q)).trans (hb q).2
  have h₂ := mul_le_mul_of_nonneg_right hb₂ (sq_nonneg ‖x‖)
  have hxsC := mul_le_mul_of_nonneg_left hxs (show 0≤C by linarith)
  have h₁ := mul_le_mul_of_nonneg_left hb₁ (show 0≤2*(n:ℝ)*δ by positivity)
  have hδC := mul_le_mul_of_nonneg_left hδ1 (show 0≤2*(n:ℝ)*C by positivity)
  have he : δ*(Δ (euclideanInteriorTorsion n R δ)) x=
      4*deriv (deriv boundaryTorsionProfile) q*‖x‖^2-
        2*(n:ℝ)*δ*deriv boundaryTorsionProfile q := by
    rw [euclideanInteriorTorsion_laplacian R hδ]
    dsimp only [q]
    field_simp
  apply (le_div_iff₀ hδ).mpr
  nlinarith

end RegularPointCoordinates

end

end OAI
