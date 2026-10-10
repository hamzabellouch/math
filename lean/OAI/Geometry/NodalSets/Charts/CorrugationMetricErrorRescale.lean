import OAI.Geometry.NodalSets.Elliptic.CorrugationRegimeErrors

namespace OAI

namespace Yau.Geometry
open Yau.Jets
open scoped ContDiff
noncomputable section

lemma corrugationMetricError_smul_both
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (χ : Coord → ℝ) (f : (ℝ × ℝ) → ℝ)
    (s J R : ℝ) (a b : Coord →L[ℝ] ℝ) (y x u v : Coord) (r : ℝ) :
    corrugationMetricError g χ f s J R a b y x (r • u) (r • v) =
      r^2*corrugationMetricError g χ f s J R a b y x u v := by
  simp only [corrugationMetricError,map_smul,smul_apply,smul_eq_mul]
  ring

lemma corrugationMetricError_bound_rescale
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (χ : Coord → ℝ) (f : (ℝ × ℝ) → ℝ)
    (s J R : ℝ) (a b : Coord →L[ℝ] ℝ) (y x : Coord)
    {K B : ℝ} (hK : 0 < K)
    (hb : ∀ u v : Coord, ‖u‖ ≤ 1 → ‖v‖ ≤ 1 →
      |corrugationMetricError g χ f s J R a b y x u v| ≤ B)
    (u v : Coord) (hu : ‖u‖ ≤ K) (hv : ‖v‖ ≤ K) :
    |corrugationMetricError g χ f s J R a b y x u v| ≤ K^2*B := by
  have hnorm (w : Coord) (hw : ‖w‖ ≤ K) : ‖K⁻¹ • w‖ ≤ 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hK)]
    exact (mul_le_mul_of_nonneg_left hw (inv_nonneg.mpr hK.le)).trans_eq (inv_mul_cancel₀ hK.ne')
  have h := hb (K⁻¹ • u) (K⁻¹ • v) (hnorm u hu) (hnorm v hv)
  have hid : corrugationMetricError g χ f s J R a b y x u v =
      K^2*corrugationMetricError g χ f s J R a b y x (K⁻¹ • u) (K⁻¹ • v) := by
    rw [corrugationMetricError_smul_both]
    field_simp
  rw [hid,abs_mul,abs_of_nonneg (sq_nonneg K)]
  exact mul_le_mul_of_nonneg_left h (sq_nonneg K)

theorem corrugation_actual_bounded_regime_errors (χ : Coord → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcpt : HasCompactSupport χ)
    (hχrange : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1) {D : ℝ} (hD : 0 < D)
    (hχD : ∀ z, ‖fderiv ℝ χ z‖ ≤ D*(χ z)^((7:ℝ)/8))
    {amp K G V : ℝ} (hamp : 0 ≤ amp) (hamp1 : amp ≤ 1)
    (hK : 0 ≤ K) (hG : 0 ≤ G) (hV : 0 < V) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (s L : ℝ),
      0 ≤ s → 0 < L → ∀ k : ℕ,
      ∀ (a b : Coord →L[ℝ] ℝ) (y x u v : Coord),
      ‖u‖ ≤ V → ‖v‖ ≤ V → ‖a.prod b‖ ≤ K →
      ‖metricConnection (g x) (fderiv ℝ g x)‖ ≤ G →
      let χ₀ := χ ((corrugationScale L k)⁻¹ • (x-y))
      let l := corrugationSlope amp (1/4)
        (corrugationCellRadius (corrugationFastMap (corrugationFrequency k) a b (x-y)))
      ∀ T : ℝ, 0 < T →
      (corrugationFrequency k*χ₀*l ≤ T →
        |corrugationMetricError g χ (corrugationPeriodicWell amp) s (corrugationFrequency k)
          (corrugationScale L k) a b y x u v| ≤ C*s*corrugationLowErrorRate L T k) ∧
      (T < corrugationFrequency k*χ₀*l →
        |corrugationMetricError g χ (corrugationPeriodicWell amp) s (corrugationFrequency k)
          (corrugationScale L k) a b y x u v| ≤
            C*s*corrugationHighErrorRate L T k*(corrugationFrequency k*χ₀*l)) := by
  obtain ⟨C,hC,hbound⟩ := corrugation_actual_regime_errors χ hχ hcpt hχrange hD hχD hamp hamp1 hK hG
  refine ⟨V^2*C,mul_pos (sq_pos_of_pos hV) hC,?_⟩
  intro g s L hs hL k a b y x u v hu hv hab hΓ χ₀ l T hT
  constructor
  · intro hreg
    have hb := corrugationMetricError_bound_rescale g χ (corrugationPeriodicWell amp) s
      (corrugationFrequency k) (corrugationScale L k) a b y x hV
      (fun u v hu hv ↦ (hbound g s L hs hL k a b y x u v hu hv hab hΓ T hT).1 hreg) u v hu hv
    exact hb.trans_eq (by ring)
  · intro hreg
    have hb := corrugationMetricError_bound_rescale g χ (corrugationPeriodicWell amp) s
      (corrugationFrequency k) (corrugationScale L k) a b y x hV
      (fun u v hu hv ↦ (hbound g s L hs hL k a b y x u v hu hv hab hΓ T hT).2 hreg) u v hu hv
    exact hb.trans_eq (by ring)

end
end Yau.Geometry

end OAI
