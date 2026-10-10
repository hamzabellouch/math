import OAI.Geometry.NodalSets.Elliptic.CorrugationErrorBound

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
open scoped ContDiff
noncomputable section

lemma clm_apply_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) {C : ℝ} (hA : ‖A‖ ≤ C) (v : E) : ‖A v‖ ≤ C*‖v‖ :=
  (A.le_opNorm v).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg v))

lemma clm_unit_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) {C : ℝ} (hA : ‖A‖ ≤ C) (v : E) (hv : ‖v‖ ≤ 1) : ‖A v‖ ≤ C := by
  exact (clm_apply_bound A hA v).trans (by nlinarith [norm_nonneg A])

lemma bilinear_unit_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] E →L[ℝ] F) {C : ℝ} (hA : ‖A‖ ≤ C)
    (u v : E) (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) : ‖A u v‖ ≤ C :=
  clm_unit_bound (A u) (clm_unit_bound A hA u hu) v hv

lemma compact_second_derivative_bound (χ : Coord → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) : ∃ C : ℝ, 0 < C ∧ ∀ x, ‖fderiv ℝ (fderiv ℝ χ) x‖ ≤ C := by
  have hsub : tsupport (fderiv ℝ (fderiv ℝ χ)) ⊆ tsupport χ :=
    (tsupport_fderiv_subset ℝ (f := fderiv ℝ χ)).trans (tsupport_fderiv_subset ℝ (f := χ))
  have hcDD : IsCompact (tsupport (fderiv ℝ (fderiv ℝ χ))) :=
    hc.of_isClosed_subset isClosed_closure hsub
  have hcont : Continuous (fun x ↦ ‖fderiv ℝ (fderiv ℝ χ) x‖) :=
    ((hχ.fderiv_right (m := ∞) (by simp)).continuous_fderiv (by simp)).norm
  obtain ⟨B,hB⟩ := (hcDD.image hcont).bddAbove
  refine ⟨max B 0+1,by positivity,fun x ↦ ?_⟩
  by_cases hx : x ∈ tsupport (fderiv ℝ (fderiv ℝ χ))
  · exact (hB ⟨x,hx,rfl⟩).trans (by linarith [le_max_left B 0])
  · have hz : fderiv ℝ (fderiv ℝ χ) x = 0 := by
      by_contra hn
      exact hx (subset_tsupport _ hn)
    rw [hz]
    simp only [ContinuousLinearMap.opNorm_zero]
    positivity

lemma corrugationMetricError_operator_bound
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (χ : Coord → ℝ) (f : (ℝ × ℝ) → ℝ)
    {s J R C₀ C₁ C₂ L K G : ℝ}
    (hs : 0 ≤ s) (hJ : 0 < J) (hR : 0 < R)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hL : 0 ≤ L) (hK : 0 ≤ K) (hG : 0 ≤ G)
    (a b : Coord →L[ℝ] ℝ) (y x u v : Coord) (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hc : 0 ≤ χ (R⁻¹ • (x-y)))
    (hf : |f (corrugationFastMap J a b (x-y))| ≤ C₀)
    (hχD : ‖fderiv ℝ χ (R⁻¹ • (x-y))‖ ≤ C₁)
    (hχDD : ‖fderiv ℝ (fderiv ℝ χ) (R⁻¹ • (x-y))‖ ≤ C₂)
    (hfD : ‖fderiv ℝ f (corrugationFastMap J a b (x-y))‖ ≤ L)
    (hQ : ‖a.prod b‖ ≤ K)
    (hΓ : ‖metricConnection (g x) (fderiv ℝ g x)‖ ≤ G) :
    |corrugationMetricError g χ f s J R a b y x u v| ≤
      s*(2*C₁*(L*K)/R + C₀*C₂/(J*R^2) +
        χ (R⁻¹ • (x-y))*(L*K)*G + C₀*C₁*G/(J*R)) := by
  have hD (w : Coord) : |fderiv ℝ f (corrugationFastMap J a b (x-y)) (a.prod b w)| ≤
      (L*K)*‖w‖ := by
    calc
      _ ≤ L*‖a.prod b w‖ := clm_apply_bound _ hfD _
      _ ≤ L*(K*‖w‖) := mul_le_mul_of_nonneg_left (clm_apply_bound _ hQ _) hL
      _ = _ := by ring
  have hconn := bilinear_unit_bound _ hΓ u v hu hv
  apply corrugationMetricError_bound g χ f hs hJ hR hC₀ hC₁ hC₂ (mul_nonneg hL hK) hG a b y x u v hc hf
  · exact clm_unit_bound _ hχD u hu
  · exact clm_unit_bound _ hχD v hv
  · exact bilinear_unit_bound _ hχDD u v hu hv
  · exact (hD u).trans (by nlinarith [mul_nonneg hL hK])
  · exact (hD v).trans (by nlinarith [mul_nonneg hL hK])
  · exact (hD _).trans (mul_le_mul_of_nonneg_left hconn (mul_nonneg hL hK))
  · exact (clm_apply_bound _ hχD _).trans (mul_le_mul_of_nonneg_left hconn hC₁)

end
end Yau.Geometry

end OAI
