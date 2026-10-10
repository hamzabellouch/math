import OAI.Geometry.NodalSets.Charts.CorrugationMetricError

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section

lemma corrugationMetricError_bound
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (χ : Coord → ℝ) (f : (ℝ × ℝ) → ℝ)
    {s J R C₀ C₁ C₂ L G : ℝ}
    (hs : 0 ≤ s) (hJ : 0 < J) (hR : 0 < R)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hL : 0 ≤ L) (hG : 0 ≤ G)
    (a b : Coord →L[ℝ] ℝ) (y x u v : Coord)
    (hc : 0 ≤ χ (R⁻¹ • (x-y)))
    (hf : |f (corrugationFastMap J a b (x-y))| ≤ C₀)
    (hχu : |fderiv ℝ χ (R⁻¹ • (x-y)) u| ≤ C₁)
    (hχv : |fderiv ℝ χ (R⁻¹ • (x-y)) v| ≤ C₁)
    (hχuv : |fderiv ℝ (fderiv ℝ χ) (R⁻¹ • (x-y)) u v| ≤ C₂)
    (hfu : |fderiv ℝ f (corrugationFastMap J a b (x-y)) (a.prod b u)| ≤ L)
    (hfv : |fderiv ℝ f (corrugationFastMap J a b (x-y)) (a.prod b v)| ≤ L)
    (hfΓ : |fderiv ℝ f (corrugationFastMap J a b (x-y))
      (a.prod b (metricConnection (g x) (fderiv ℝ g x) u v))| ≤ L*G)
    (hχΓ : |fderiv ℝ χ (R⁻¹ • (x-y))
      (metricConnection (g x) (fderiv ℝ g x) u v)| ≤ C₁*G) :
    |corrugationMetricError g χ f s J R a b y x u v| ≤
      s*(2*C₁*L/R + C₀*C₂/(J*R^2) + χ (R⁻¹ • (x-y))*L*G + C₀*C₁*G/(J*R)) := by
  let X := R⁻¹ • (x-y)
  let Z := corrugationFastMap J a b (x-y)
  let Γ := metricConnection (g x) (fderiv ℝ g x) u v
  have hcross : |fderiv ℝ χ X v*fderiv ℝ f Z (a.prod b u) +
      fderiv ℝ χ X u*fderiv ℝ f Z (a.prod b v)| ≤ 2*C₁*L := by
    calc
      _ ≤ |fderiv ℝ χ X v*fderiv ℝ f Z (a.prod b u)| +
          |fderiv ℝ χ X u*fderiv ℝ f Z (a.prod b v)| := abs_add_le _ _
      _ ≤ C₁*L+C₁*L := by
        simp only [abs_mul]
        exact add_le_add (mul_le_mul hχv hfu (abs_nonneg _) hC₁)
          (mul_le_mul hχu hfv (abs_nonneg _) hC₁)
      _ = _ := by ring
  have h1 : |s/R*(fderiv ℝ χ X v*fderiv ℝ f Z (a.prod b u) +
      fderiv ℝ χ X u*fderiv ℝ f Z (a.prod b v))| ≤ (s/R)*(2*C₁*L) := by
    rw [abs_mul,abs_of_nonneg (div_nonneg hs hR.le)]
    exact mul_le_mul_of_nonneg_left hcross (div_nonneg hs hR.le)
  have h2 : |s/(J*R^2)*f Z*fderiv ℝ (fderiv ℝ χ) X u v| ≤ s/(J*R^2)*C₀*C₂ := by
    simp only [abs_mul,abs_of_nonneg (div_nonneg hs (mul_nonneg hJ.le (sq_nonneg R))) ]
    exact mul_le_mul_of_nonneg (mul_le_mul_of_nonneg_left hf (by positivity)) hχuv
      (mul_nonneg (div_nonneg hs (mul_nonneg hJ.le (sq_nonneg R))) (abs_nonneg _)) hC₂
  have h3 : |s*χ X*fderiv ℝ f Z (a.prod b Γ)| ≤ s*χ X*(L*G) := by
    rw [abs_mul,abs_of_nonneg (mul_nonneg hs hc)]
    exact mul_le_mul_of_nonneg (le_refl _) hfΓ (mul_nonneg hs hc) (mul_nonneg hL hG)
  have h4 : |s/(J*R)*f Z*fderiv ℝ χ X Γ| ≤ s/(J*R)*C₀*(C₁*G) := by
    simp only [abs_mul,abs_of_nonneg (div_nonneg hs (mul_nonneg hJ.le hR.le))]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hf (by positivity)) hχΓ (abs_nonneg _) (by positivity)
  have hsub (a b : ℝ) : |a-b| ≤ |a|+|b| := by
    simpa only [sub_eq_add_neg,abs_neg] using abs_add_le a (-b)
  unfold corrugationMetricError
  calc
    _ ≤ (|s/R*(fderiv ℝ χ X v*fderiv ℝ f Z (a.prod b u) +
        fderiv ℝ χ X u*fderiv ℝ f Z (a.prod b v))| +
        |s/(J*R^2)*f Z*fderiv ℝ (fderiv ℝ χ) X u v|) +
        |s*χ X*fderiv ℝ f Z (a.prod b Γ)| + |s/(J*R)*f Z*fderiv ℝ χ X Γ| := by
      exact (hsub _ _).trans (add_le_add
        ((hsub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    _ ≤ s/R*(2*C₁*L)+s/(J*R^2)*C₀*C₂+s*χ X*(L*G)+s/(J*R)*C₀*(C₁*G) :=
      add_le_add (add_le_add (add_le_add h1 h2) h3) h4
    _ = _ := by dsimp [X]; ring

end
end Yau.Geometry

end OAI
