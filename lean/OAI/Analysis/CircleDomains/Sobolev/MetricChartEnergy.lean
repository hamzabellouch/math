import OAI.Analysis.CircleDomains.Uniformization.MetricConformality
import OAI.Analysis.CircleDomains.Sobolev.EnergyChangeCoordinates

namespace OAI

/-!
# Energy of the actual metric-conformal chart differential

The Gram equations defining metric conformality identify the source
metric with a scalar multiple of the pulled-back Euclidean metric.
Consequently the covector energy changes by the positive Jacobian.
-/

open Matrix

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

def complexRealMatrix (A : ℂ →L[ℝ] ℂ) : PlanarMetric :=
  !![(A 1).re, (A Complex.I).re; (A 1).im, (A Complex.I).im]

theorem det_complexRealMatrix (A : ℂ →L[ℝ] ℂ) :
    (complexRealMatrix A).det =
      (A 1).re * (A Complex.I).im - (A Complex.I).re * (A 1).im := by
  simp [complexRealMatrix, Matrix.det_fin_two]

theorem metric_eq_scaled_chart_gram
    {g : (ℝ × ℝ) → PlanarMetric} {f : Sphere → Sphere} {p : Sphere}
    (hf : IsMetricConformalAt g f p) (hg : (sphereChartMetric g p).IsSymm) :
    ∃ c : ℝ, 0 < c ∧ sphereChartMetric g p = c •
      ((complexRealMatrix (fderiv ℝ (sphereLocalMap f p) (chart p p)))ᵀ *
        complexRealMatrix (fderiv ℝ (sphereLocalMap f p) (chart p p))) := by
  obtain ⟨_, _, scale, hscale, hxx, hyy, hxy, _⟩ := hf
  refine ⟨scale⁻¹, inv_pos.mpr hscale, ?_⟩
  have hsym : sphereChartMetric g p 1 0 = sphereChartMetric g p 0 1 := by
    exact congrFun (congrFun hg 0) 1
  have hgram :
      (complexRealMatrix (fderiv ℝ (sphereLocalMap f p) (chart p p)))ᵀ *
        complexRealMatrix (fderiv ℝ (sphereLocalMap f p) (chart p p)) =
      scale • sphereChartMetric g p := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [complexRealMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply] <;>
      nlinarith [hxx, hyy, hxy, hsym]
  rw [hgram, smul_smul, inv_mul_cancel₀ hscale.ne', one_smul]

theorem IsMetricConformalAt.covectorEnergy
    {g : (ℝ × ℝ) → PlanarMetric} {f : Sphere → Sphere} {p : Sphere}
    (hf : IsMetricConformalAt g f p) (hg : (sphereChartMetric g p).IsSymm)
    (v : Fin 2 → ℝ) :
    covectorEnergy
      ((complexRealMatrix (fderiv ℝ (sphereLocalMap f p) (chart p p)))ᵀ *ᵥ v)
      (sphereChartMetric g p) =
    (complexRealMatrix (fderiv ℝ (sphereLocalMap f p) (chart p p))).det *
      covectorEnergy v 1 := by
  obtain ⟨c, hc, heq⟩ := metric_eq_scaled_chart_gram hf hg
  have hdet : 0 < (complexRealMatrix (fderiv ℝ (sphereLocalMap f p) (chart p p))).det := by
    rw [det_complexRealMatrix]
    exact hf.2.2.choose_spec.2.2.2.2
  rw [heq]
  have henergy := covectorEnergy_conformal_pullback v Matrix.PosDef.one hdet.ne' hc
  simpa only [mul_one, abs_of_pos hdet] using henergy

end CircleDomainRigidity

end

end OAI
