import OAI.Geometry.IsometricImmersion.Immersions.InducedMetric
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

def matrixContinuousLinear (R : Matrix (Fin 2) (Fin 2) ℝ) : Coord →L[ℝ] Coord :=
  LinearMap.toContinuousLinearMap R.mulVecLin

@[simp] theorem matrixContinuousLinear_apply (R : Matrix (Fin 2) (Fin 2) ℝ) (v : Coord) :
    matrixContinuousLinear R v = R *ᵥ v := rfl

def affineCoordinates (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (q : Coord) : Coord :=
  b + R *ᵥ q

def affinePullbackMetric (g : MetricField) (b : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) : MetricField := fun q =>
  Rᵀ * g (affineCoordinates b R q) * R

def affinePullbackImmersion (F : Coord → Ambient) (b : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) : Coord → Ambient :=
  F ∘ affineCoordinates b R

theorem affineCoordinates_contDiff (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) :
    ContDiff ℝ ∞ (affineCoordinates b R) :=
  contDiff_const.add (matrixContinuousLinear R).contDiff

theorem affineCoordinates_hasFDerivAt (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ)
    (q : Coord) : HasFDerivAt (affineCoordinates b R) (matrixContinuousLinear R) q := by
  change HasFDerivAt (fun x => b + matrixContinuousLinear R x)
    (matrixContinuousLinear R) q
  exact (matrixContinuousLinear R).hasFDerivAt.const_add b

theorem affineCoordinates_fderiv (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ)
    (q : Coord) : fderiv ℝ (affineCoordinates b R) q = matrixContinuousLinear R :=
  (affineCoordinates_hasFDerivAt b R q).fderiv

@[simp] theorem affineCoordinates_zero (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) :
    affineCoordinates b R 0 = b := by simp [affineCoordinates]

theorem isOpen_affine_preimage {U : Set Coord} (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) :
    IsOpen (affineCoordinates b R ⁻¹' U) :=
  hU.preimage (affineCoordinates_contDiff b R).continuous

theorem affine_comp_contDiffOn {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} {U : Set Coord} (hf : ContDiffOn ℝ ∞ f U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) :
    ContDiffOn ℝ ∞ (f ∘ affineCoordinates b R) (affineCoordinates b R ⁻¹' U) :=
  hf.comp (affineCoordinates_contDiff b R).contDiffOn (fun _ hq => hq)

theorem fderiv_affine_comp_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (q v : Coord)
    (hf : DifferentiableAt ℝ f (affineCoordinates b R q)) :
    fderiv ℝ (f ∘ affineCoordinates b R) q v =
      fderiv ℝ f (affineCoordinates b R q) (R *ᵥ v) := by
  rw [fderiv_comp q hf (affineCoordinates_hasFDerivAt b R q).differentiableAt,
    affineCoordinates_fderiv, ContinuousLinearMap.comp_apply, matrixContinuousLinear_apply]

theorem matrix_pullback_bilinear (G R : Matrix (Fin 2) (Fin 2) ℝ) (v w : Coord) :
    (R *ᵥ v) ⬝ᵥ (G *ᵥ (R *ᵥ w)) = v ⬝ᵥ ((Rᵀ * G * R) *ᵥ w) := by
  calc
    _ = (G *ᵥ (R *ᵥ w)) ⬝ᵥ (R *ᵥ v) := dotProduct_comm _ _
    _ = v ⬝ᵥ (Rᵀ *ᵥ (G *ᵥ (R *ᵥ w))) :=
      (Matrix.dotProduct_transpose_mulVec R v (G *ᵥ (R *ᵥ w))).symm
    _ = _ := by rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem affinePullbackMetric_smoothPositive {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ)
    (hR : Function.Injective R.mulVec) :
    SmoothPositiveOn (affinePullbackMetric g b R) (affineCoordinates b R ⁻¹' U) := by
  constructor
  · intro i j
    have hc (a k : Fin 2) : ContDiffOn ℝ ∞
        (fun q => g (affineCoordinates b R q) a k) (affineCoordinates b R ⁻¹' U) :=
      affine_comp_contDiffOn (hg.1 a k) b R
    simp only [affinePullbackMetric, Matrix.mul_apply, Matrix.transpose_apply]
    apply ContDiffOn.sum
    intro k _
    apply ContDiffOn.mul _ contDiffOn_const
    apply ContDiffOn.sum
    intro a _
    exact contDiffOn_const.mul (hc a k)
  · intro q hq
    simpa only [affinePullbackMetric, Matrix.conjTranspose_eq_transpose_of_trivial] using
      (hg.2 (affineCoordinates b R q) hq).conjTranspose_mul_mul_same hR

theorem affinePullbackImmersion_isometric {g : MetricField} {F : Coord → Ambient}
    {U : Set Coord} (hF : IsometricOn g F U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) :
    IsometricOn (affinePullbackMetric g b R) (affinePullbackImmersion F b R)
      (affineCoordinates b R ⁻¹' U) := by
  refine ⟨affine_comp_contDiffOn hF.1 b R, ?_⟩
  intro q hq v w
  have hd : DifferentiableAt ℝ F (affineCoordinates b R q) :=
    (((hF.1 _ hq).contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp))
  change inner ℝ (fderiv ℝ (F ∘ affineCoordinates b R) q v)
    (fderiv ℝ (F ∘ affineCoordinates b R) q w) = _
  rw [fderiv_affine_comp_apply b R q v hd, fderiv_affine_comp_apply b R q w hd,
    hF.2 (affineCoordinates b R q) hq]
  exact matrix_pullback_bilinear (g (affineCoordinates b R q)) R v w

theorem mulVec_injective_of_transpose_mul_eq_one
    (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : Rᵀ * R = 1) : Function.Injective R.mulVec := by
  intro v w hvw
  have h := congrArg (fun u : Coord => Rᵀ *ᵥ u) hvw
  simpa only [Matrix.mulVec_mulVec, hR, Matrix.one_mulVec] using h

end SmoothLocal.Geometry

end

end OAI
