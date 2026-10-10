import OAI.Geometry.IsometricImmersion.Metrics.ModelProfile
import OAI.Geometry.IsometricImmersion.Curvature.PrescribedCurvature
import OAI.Geometry.IsometricImmersion.Curvature.AffineCurvature

namespace OAI

noncomputable section
open Set
open scoped ContDiff Matrix

namespace SmoothLocal.Model
open SmoothLocal.Geometry SmoothLocal.ODE

def quarterMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![(1 / 4 : ℝ), 0; 0, 1 / 4]

theorem quarterMatrix_isUnit : IsUnit quarterMatrix := by
  apply (Matrix.isUnit_iff_isUnit_det _).2
  apply isUnit_iff_ne_zero.mpr
  norm_num [quarterMatrix, Matrix.det_fin_two]

theorem quarterCoordinates_eq (p : Coord) :
    affineCoordinates 0 quarterMatrix p = (1 / 4 : ℝ) • p := by
  ext i
  fin_cases i <;> simp [affineCoordinates, quarterMatrix,
    dotProduct, Fin.sum_univ_two]

def scaledModelCurvature (kappa : ℝ) (p : Coord) : ℝ :=
  modelCurvature kappa ((4 : ℝ) • p)

theorem scaledModelCurvature_contDiff (kappa : ℝ) :
    ContDiff ℝ ∞ (scaledModelCurvature kappa) := by
  have hd : ContDiff ℝ ∞ (fun p : Coord => (4 : ℝ) • p) :=
    contDiff_const_smul (4 : ℝ)
  exact (modelCurvature_contDiff kappa).comp hd

theorem scaledModelCurvature_bound {kappa : ℝ} (hk : 0 ≤ kappa)
    {p : Coord} (hp : p ∈ square) : |scaledModelCurvature kappa p| ≤ 31 * kappa := by
  have hx : (4 * p 0) ^ 2 ≤ (4 : ℝ) ^ 2 := sq_le_sq'
    (by linarith [(hp 0).1]) (by linarith [(hp 0).2])
  have hy : (4 * p 1) ^ 2 ≤ (4 : ℝ) ^ 2 := sq_le_sq'
    (by linarith [(hp 1).1]) (by linarith [(hp 1).2])
  have hh := modelProfile_bounds (4 * p 1)
  have hb : |(4 * p 0) ^ 2 - modelProfile (4 * p 1)| ≤ 31 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (4 * p 0)]
  change |kappa * ((4 * p 0) ^ 2 - modelProfile (4 * p 1))| ≤ _
  rw [abs_mul, abs_of_nonneg hk]
  nlinarith only [mul_le_mul_of_nonneg_left hb hk]

def modelMetricDomain : Set Coord := affineCoordinates 0 quarterMatrix ⁻¹' square

theorem modelMetricDomain_isOpen : IsOpen modelMetricDomain :=
  isOpen_affine_preimage coordinate_square_isOpen 0 quarterMatrix

theorem modelMetricDomain_contains_model_square :
    Icc (fun _ : Fin 2 => (-3 : ℝ)) (fun _ => (3 : ℝ)) ⊆ modelMetricDomain := by
  intro p hp
  change affineCoordinates 0 quarterMatrix p ∈ square
  rw [quarterCoordinates_eq]
  intro i
  change -1 < (1 / 4 : ℝ) * p i ∧ (1 / 4 : ℝ) * p i < 1
  constructor <;> linarith [hp.1 i, hp.2 i]

def constructedModelMetric (kappa : ℝ) : MetricField :=
  affinePullbackMetric (prescribedCurvatureMetric (scaledModelCurvature kappa))
    0 quarterMatrix

theorem constructedModelMetric_spec {kappa : ℝ}
    (hk : 0 < kappa) (hkSmall : kappa ≤ (1 : ℝ) / 31000) :
    SmoothPositiveOn (constructedModelMetric kappa) modelMetricDomain ∧
      (∀ p ∈ modelMetricDomain,
        gaussianCurvature (constructedModelMetric kappa) p = modelCurvature kappa p) := by
  have hK := (scaledModelCurvature_contDiff kappa).contDiffOn (s := square)
  have hbound : ∀ p ∈ square, |scaledModelCurvature kappa p| ≤ (1 : ℝ) / 1000 := by
    intro p hp
    exact (scaledModelCurvature_bound hk.le hp).trans (by linarith)
  have hg := prescribedCurvatureMetric_smoothPositiveOn hK hbound
  refine ⟨affinePullbackMetric_smoothPositive hg 0 quarterMatrix
    (Matrix.mulVec_injective_of_isUnit quarterMatrix_isUnit), ?_⟩
  intro p hp
  change gaussianCurvature
    (affinePullbackMetric (prescribedCurvatureMetric (scaledModelCurvature kappa)) 0 quarterMatrix) p = _
  rw [gaussianCurvature_affinePullback hg coordinate_square_isOpen 0 quarterMatrix
    quarterMatrix_isUnit p hp, prescribedCurvatureMetric_gaussianCurvature hK hbound hp]
  unfold scaledModelCurvature
  rw [quarterCoordinates_eq, smul_smul]
  norm_num

theorem constructedModelMetric_central_curvature {kappa : ℝ}
    (hk : 0 < kappa) (hkSmall : kappa ≤ (1 : ℝ) / 31000) {p : Coord}
    (hp : ∀ i : Fin 2, p i ∈ Icc (-(1 / 5 : ℝ)) (1 / 5)) :
    gaussianCurvature (constructedModelMetric kappa) p < -kappa / 2 := by
  have hS : p ∈ Icc (fun _ : Fin 2 => (-3 : ℝ)) (fun _ => (3 : ℝ)) := by
    constructor <;> intro i <;> linarith [(hp i).1, (hp i).2]
  rw [(constructedModelMetric_spec hk hkSmall).2 p (modelMetricDomain_contains_model_square hS)]
  exact modelCurvature_central_square hk hp

end SmoothLocal.Model

end

end OAI
