import OAI.Geometry.NodalSets.Elliptic.CorrugationGlobalJets
import OAI.Geometry.NodalSets.Elliptic.CorrugationNormBounds

namespace OAI

namespace Yau.Geometry
open Yau.Jets Real
open scoped ContDiff
noncomputable section

theorem corrugation_global_source_error_bound (χ : Coord → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcpt : HasCompactSupport χ)
    (hχrange : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1) {D : ℝ} (hD : 0 < D)
    (hχD : ∀ z, ‖fderiv ℝ χ z‖ ≤ D*(χ z)^((7:ℝ)/8))
    {amp K G : ℝ} (hamp : 0 ≤ amp) (hK : 0 ≤ K) (hG : 0 ≤ G) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (s J R : ℝ),
      0 ≤ s → 0 < J → 0 < R →
      ∀ (a b : Coord →L[ℝ] ℝ) (y x u v : Coord),
      ‖u‖ ≤ 1 → ‖v‖ ≤ 1 → ‖a.prod b‖ ≤ K →
      ‖metricConnection (g x) (fderiv ℝ g x)‖ ≤ G →
      |corrugationMetricError g χ (corrugationPeriodicWell amp) s J R a b y x u v| ≤
        C*s*(R⁻¹*(χ (R⁻¹ • (x-y)))^((7:ℝ)/8)*corrugationSlope amp (1/4) (corrugationCellRadius (corrugationFastMap J a b (x-y))) +
          (J*R^2)⁻¹ + χ (R⁻¹ • (x-y))*corrugationSlope amp (1/4) (corrugationCellRadius (corrugationFastMap J a b (x-y))) + (J*R)⁻¹) := by
  obtain ⟨B,hB,hf⟩ := corrugationPeriodicWell_bounded amp
  obtain ⟨M,hM,hχDD⟩ := compact_second_derivative_bound χ hχ hcpt
  let C := 4*D*K+B*M+2*K*G+B*D*G+1
  have hC : 0 < C := by dsimp [C]; positivity
  have h1 : 4*D*K ≤ C := by dsimp [C]; nlinarith [mul_nonneg hB.le hM.le,mul_nonneg hK hG,mul_nonneg (mul_nonneg hB.le hD.le) hG]
  have h2 : B*M ≤ C := by dsimp [C]; nlinarith [mul_nonneg hD.le hK,mul_nonneg hK hG,mul_nonneg (mul_nonneg hB.le hD.le) hG]
  have h3 : 2*K*G ≤ C := by dsimp [C]; nlinarith [mul_nonneg hD.le hK,mul_nonneg hB.le hM.le,mul_nonneg (mul_nonneg hB.le hD.le) hG]
  have h4 : B*D*G ≤ C := by dsimp [C]; nlinarith [mul_nonneg hD.le hK,mul_nonneg hB.le hM.le,mul_nonneg hK hG]
  refine ⟨C,hC,?_⟩
  intro g s J R hs hJ hR a b y x u v hu hv hQ hΓ
  let q := (χ (R⁻¹ • (x-y)))^((7:ℝ)/8)
  let l := corrugationSlope amp (1/4) (corrugationCellRadius (corrugationFastMap J a b (x-y)))
  have hq : 0 ≤ q := Real.rpow_nonneg (hχrange _).1 _
  have hq1 : q ≤ 1 := Real.rpow_le_one (hχrange _).1 (hχrange _).2 (by norm_num)
  have hl : 0 ≤ l := corrugationSlope_nonneg hamp (corrugationCellRadius_properties _).1
  have hfD : ‖fderiv ℝ (corrugationPeriodicWell amp) (corrugationFastMap J a b (x-y))‖ ≤ 2*l := by
    exact corrugationPeriodicWell_global_derivative_bound hamp _
  have hb := corrugationMetricError_operator_bound g χ (corrugationPeriodicWell amp)
    hs hJ hR hB.le (mul_nonneg hD.le hq) hM.le (show 0 ≤ 2*l by positivity) hK hG
    a b y x u v hu hv (hχrange _).1 (hf _) (hχD _) (hχDD _) hfD hQ hΓ
  have hn1 : 0 ≤ R⁻¹*q*l := by positivity
  have hn2 : 0 ≤ (J*R^2)⁻¹ := by positivity
  have hn3 : 0 ≤ χ (R⁻¹ • (x-y))*l := mul_nonneg (hχrange _).1 hl
  have hn4 : 0 ≤ (J*R)⁻¹ := by positivity
  have hd4 : B*D*G*q ≤ C :=
    (mul_le_mul_of_nonneg_left hq1 (by positivity)).trans (by simpa using h4)
  calc
    _ ≤ s*(2*(D*q)*(2*l*K)/R+B*M/(J*R^2)+χ (R⁻¹ • (x-y))*(2*l*K)*G+B*(D*q)*G/(J*R)) := hb
    _ = s*((4*D*K)*(R⁻¹*q*l)+(B*M)*(J*R^2)⁻¹+
        (2*K*G)*(χ (R⁻¹ • (x-y))*l)+(B*D*G*q)*(J*R)⁻¹) := by ring
    _ ≤ s*(C*(R⁻¹*q*l)+C*(J*R^2)⁻¹+C*(χ (R⁻¹ • (x-y))*l)+C*(J*R)⁻¹) := by
      exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add
        (add_le_add (mul_le_mul_of_nonneg_right h1 hn1) (mul_le_mul_of_nonneg_right h2 hn2))
        (mul_le_mul_of_nonneg_right h3 hn3)) (mul_le_mul_of_nonneg_right hd4 hn4)) hs
    _ = _ := by dsimp [q,l]; ring

end
end Yau.Geometry

end OAI
