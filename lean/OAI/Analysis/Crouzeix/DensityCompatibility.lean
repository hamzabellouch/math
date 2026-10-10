import Mathlib
import OAI.Analysis.Crouzeix.Density
import OAI.Analysis.Crouzeix.DiskEndpoint
import OAI.Analysis.Crouzeix.TensorDensity

namespace OAI

/-! Density Compatibility. -/

noncomputable section

open MeasureTheory

open scoped InnerProductSpace TensorProduct Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace CrouzeixHilbert

namespace Boundary

def toHSCLM (n : ℕ) : Coeff n →L[ℂ] HS n :=
  ({ toFun := toHS
     map_add' := fun _ _ => by apply PiLp.ext; intro ij; rfl
     map_smul' := fun _ _ => by apply PiLp.ext; intro ij; rfl } :
      Coeff n →ₗ[ℂ] HS n).toContinuousLinearMap

@[simp] theorem toHSCLM_apply {n : ℕ} (X : Coeff n) : toHSCLM n X = toHS X := rfl

def weightedPartialTraceCLM {n : ℕ} (X Y : Coeff n) : Coeff n →L[ℂ] Coeff n :=
  ({ toFun E := weightedPartialTrace E X Y
     map_add' E G := by simp [weightedPartialTrace, mul_add, add_mul]
     map_smul' c E := by simp [weightedPartialTrace] } :
      Coeff n →ₗ[ℂ] Coeff n).toContinuousLinearMap

@[simp] theorem weightedPartialTraceCLM_apply {n : ℕ} (E X Y : Coeff n) :
    weightedPartialTraceCLM X Y E = weightedPartialTrace E X Y := rfl

theorem integral_weightedPartialTrace {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {n : ℕ} (E : α → Coeff n) (hE : Integrable E μ) (X Y : Coeff n) :
    (∫ t, weightedPartialTrace (E t) X Y ∂μ) =
      weightedPartialTrace (∫ t, E t ∂μ) X Y :=
  (weightedPartialTraceCLM X Y).integral_comp_comm hE

def densityContinuous {n : ℕ} (E : C(CircleSpace, Coeff n)) (X Y : Coeff n) :
    C(CircleSpace, HS n) :=
  ⟨fun t => toHS (weightedPartialTrace (E t) X Y),
    (toHSCLM n).continuous.comp ((weightedPartialTraceCLM X Y).continuous.comp E.continuous)⟩

def densityLp {n : ℕ} (E : C(CircleSpace, Coeff n)) (X Y : Coeff n) : BoundaryL2 n :=
  ContinuousMap.toLp 2 circleMeasure ℂ (densityContinuous E X Y)

theorem densityLp_apply_ae {n : ℕ} (E : C(CircleSpace, Coeff n)) (X Y : Coeff n) :
    densityLp E X Y =ᵐ[circleMeasure] fun t => toHS (weightedPartialTrace (E t) X Y) :=
  ContinuousMap.coeFn_toLp _ _

theorem matrixMean_densityLp {n : ℕ} (E : C(CircleSpace, Coeff n)) (X Y : Coeff n) :
    matrixMean (densityLp E X Y) = weightedPartialTrace (∫ t, E t ∂circleMeasure) X Y := by
  rw [← integral_weightedPartialTrace E
    (E.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  ext i j
  change (∫ t, densityLp E X Y t (i,j) ∂circleMeasure) = _
  have hi : Integrable (fun t => weightedPartialTrace (E t) X Y) circleMeasure :=
    (weightedPartialTraceCLM X Y).integrable_comp
      (E.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  let e : Coeff n →L[ℂ] ℂ :=
    (PiLp.proj 2 (fun _ : Fin n × Fin n => ℂ) (i,j)).comp (toHSCLM n)
  change (∫ t, densityLp E X Y t (i,j) ∂circleMeasure) =
    e (∫ t, weightedPartialTrace (E t) X Y ∂circleMeasure)
  rw [← e.integral_comp_comm hi]
  apply integral_congr_ae
  filter_upwards [densityLp_apply_ae E X Y] with t ht
  rw [ht]
  rfl

theorem matrixMean_densityLp_mass_one {n : ℕ} (E : C(CircleSpace, Coeff n))
    (hmass : ∫ t, E t ∂circleMeasure = 1) (X Y : Coeff n) :
    matrixMean (densityLp E X Y) = (Xᴴ * Y)ᵀ := by
  rw [matrixMean_densityLp, hmass, weightedPartialTrace, mul_one]

theorem densityLp_block_posSemidef {n : ℕ} (E : C(CircleSpace, Coeff n))
    (hE : ∀ t, (E t).PosSemidef) (X Y : Coeff n) :
    ∀ᵐ t ∂circleMeasure,
      (Matrix.fromBlocks (ofHS (densityLp E X X t))
        (ofHS (densityLp E X Y t))ᴴ (ofHS (densityLp E X Y t))
        (ofHS (densityLp E Y Y t))).PosSemidef := by
  filter_upwards [densityLp_apply_ae E X X, densityLp_apply_ae E Y Y,
    densityLp_apply_ae E X Y] with t hp hq hr
  simp only [hp, hq, hr, ofHS_toHS]
  have hs : (weightedPartialTrace (E t) X Y)ᴴ = weightedPartialTrace (E t) Y X := by
    simp only [weightedPartialTrace, Matrix.conjTranspose_transpose_eq_transpose_conjTranspose,
      Matrix.conjTranspose_mul, (hE t).isHermitian.eq, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  rw [hs]
  exact weightedPartialTrace_block_posSemidef (E t) (hE t) X Y

theorem densityLp_self_hermitian {n : ℕ} (E : C(CircleSpace, Coeff n))
    (hE : ∀ t, (E t).PosSemidef) (X : Coeff n) :
    ∀ᵐ t ∂circleMeasure, (ofHS (densityLp E X X t)).IsHermitian := by
  filter_upwards [densityLp_apply_ae E X X] with t ht
  rw [ht, ofHS_toHS]
  exact ((hE t).conjTranspose_mul_mul_same X).transpose.isHermitian

end Boundary

open Boundary

theorem inner_vectorization {n : ℕ} (X Y : Coeff n) :
    ⟪vectorization X, vectorization Y⟫_ℂ = (Xᴴ * Y).trace := by
  let e : Amplification (EuclideanSpace ℂ (Fin n)) n →ₗᵢ[ℂ]
      EuclideanSpace ℂ (Fin n × Fin n) :=
    ⟨(matrixAmplificationCoordinates n n).toLinearMap, norm_matrixAmplificationCoordinates n n⟩
  rw [← e.inner_map_map]
  change ⟪matrixAmplificationCoordinates n n (vectorization X),
    matrixAmplificationCoordinates n n (vectorization Y)⟫_ℂ = _
  rw [vectorization_coordinates, vectorization_coordinates, inner_toHS]

theorem weightedPartialTrace_testing {n : ℕ} (E : Coeff n) (hE : E.IsHermitian)
    (X Y U : Coeff n) :
    ⟪toHS (weightedPartialTrace E X Y), toHS U⟫_ℂ =
      ⟪vectorization Y, tensorOperator (Matrix.toEuclideanCLM (𝕜 := ℂ) E) U
        (vectorization X)⟫_ℂ := by
  rw [tensorOperator_vectorization, inner_vectorization, inner_toHS]
  simp only [weightedPartialTrace, Matrix.conjTranspose_transpose_eq_transpose_conjTranspose,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hE.eq]
  rw [← Matrix.trace_transpose (_ * U), Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.trace_mul_comm Uᵀ]
  simp only [Matrix.mul_assoc]

end CrouzeixHilbert

end

end OAI
