import Mathlib
import OAI.Analysis.Crouzeix.DensityCompatibility

namespace OAI

/-! Boundary Fibers. -/

noncomputable section

open MeasureTheory

open scoped InnerProductSpace TensorProduct Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace CrouzeixHilbert

open Boundary

namespace Compression

section Fibres

variable {α E : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
  [CompactSpace α] [SecondCountableTopology α] {μ : Measure α} [IsFiniteMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem fibres_of_integral_interpolation (R M : C(α, E →L[ℂ] E))
    (hmass : ∫ t, star (R t) * R t ∂μ = 1)
    (hM : ∀ t, ‖M t‖ ≤ 1) (x y : E) (hN : ‖x‖ = ‖y‖)
    (hI : (∫ t, star (R t) * M t * R t ∂μ) x = y) :
    ∀ᵐ t ∂μ, M t (R t x) = R t y ∧ (M t).adjoint (R t y) = R t x := by
  let V := isometry R hmass
  let T := fieldAction (μ := μ) M M.continuous.aestronglyMeasurable 1 zero_le_one
    (Filter.Eventually.of_forall hM)
  have hT : ‖T‖ ≤ 1 := norm_fieldAction_le _ _ _ _ _
  have hIV : V.toContinuousLinearMap.adjoint (T (V x)) = y := by
    rw [integral_eq_compression R M hmass 1 zero_le_one hM] at hI
    exact hI
  obtain ⟨hf, ha⟩ := equality_in_compression V T hT x y hN hIV
  let Ms : C(α, E →L[ℂ] E) := ⟨fun t => (M t).adjoint,
    ContinuousLinearMap.adjoint.continuous.comp M.continuous⟩
  have hMsn : ∀ t, ‖Ms t‖ ≤ 1 := fun t => by
    simpa only [Ms, ContinuousMap.coe_mk, ContinuousLinearMap.adjoint.norm_map] using hM t
  have htstar : T.adjoint = fieldAction Ms Ms.continuous.aestronglyMeasurable
      1 zero_le_one (Filter.Eventually.of_forall hMsn) :=
    adjoint_fieldAction M Ms M.continuous.aestronglyMeasurable
      Ms.continuous.aestronglyMeasurable 1 zero_le_one (Filter.Eventually.of_forall hM)
      (Filter.Eventually.of_forall hMsn) (Filter.Eventually.of_forall fun _ => rfl)
  rw [htstar] at ha
  filter_upwards [fieldAction_apply_ae M M.continuous.aestronglyMeasurable
      1 zero_le_one (Filter.Eventually.of_forall hM) (V x),
    fieldAction_apply_ae Ms Ms.continuous.aestronglyMeasurable
      1 zero_le_one (Filter.Eventually.of_forall hMsn) (V y),
    lift_apply_ae R x, lift_apply_ae R y] with t hft hat hxt hyt
  constructor
  · rw [← hxt, ← hyt]
    change M t (V x t) = V y t
    rw [← hft]
    exact congrArg (fun u => u t) hf
  · rw [← hyt, ← hxt]
    change Ms t (V y t) = V x t
    rw [← hat]
    exact congrArg (fun u => u t) ha

end Fibres

end Compression

attribute [local instance] tensorDensityOperatorCompleteSpace

def matrixOperatorMap (n : ℕ) : Coeff n →L[ℂ] Operator (EuclideanSpace ℂ (Fin n)) :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).toAlgEquiv.toLinearMap.toContinuousLinearMap

@[simp] theorem matrixOperatorMap_apply {n : ℕ} (A : Coeff n) :
    matrixOperatorMap n A = Matrix.toEuclideanCLM (𝕜 := ℂ) A := rfl

def matrixBaseField {n : ℕ} (L : C(CircleSpace, Coeff n)) :
    C(CircleSpace, Operator (Amplification (EuclideanSpace ℂ (Fin n)) n)) :=
  ⟨fun t => tensorOperator (matrixOperatorMap n (L t)) (1 : Coeff n),
    (tensorOperatorCLM (1 : Coeff n)).continuous.comp
      ((matrixOperatorMap n).continuous.comp L.continuous)⟩

@[simp] theorem matrixBaseField_star_mul {n : ℕ} (L : C(CircleSpace, Coeff n))
    (t : CircleSpace) :
    star (matrixBaseField L t) * matrixBaseField L t =
      tensorOperator (matrixOperatorMap n ((L t)ᴴ * L t)) (1 : Coeff n) := by
  change star (tensorOperator _ _) * tensorOperator _ _ = _
  rw [← tensorOperator_star, ← tensorOperator_mul, star_one, one_mul]
  congr 1
  simp only [matrixOperatorMap_apply, ← Matrix.star_eq_conjTranspose, map_mul, map_star]

theorem matrixBaseField_mass {n : ℕ} (L : C(CircleSpace, Coeff n))
    (hL : ∫ t, (L t)ᴴ * L t ∂circleMeasure = 1) :
    ∫ t, star (matrixBaseField L t) * matrixBaseField L t ∂circleMeasure = 1 := by
  let : ContinuousSMul ℂ (EuclideanSpace ℂ (Fin n)) := IsBoundedSMul.continuousSMul
  let : CompleteSpace (Operator (EuclideanSpace ℂ (Fin n))) :=
    ContinuousLinearMap.instCompleteSpace
  simp only [matrixBaseField_star_mul, ← tensorOperatorCLM_apply]
  rw [(tensorOperatorCLM (H := EuclideanSpace ℂ (Fin n)) (1 : Coeff n)).integral_comp_comm,
    (matrixOperatorMap n).integral_comp_comm, hL]
  · simpa only [matrixOperatorMap_apply, tensorOperatorCLM_apply, map_one] using
      tensorOperator_one (H := EuclideanSpace ℂ (Fin n)) n
  · exact (L.continuous.star.mul L.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact (matrixOperatorMap n).integrable_comp
      ((L.continuous.star.mul L.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))

@[simp] theorem matrixBaseField_sandwich {n : ℕ} (L F : C(CircleSpace, Coeff n))
    (t : CircleSpace) :
    star (matrixBaseField L t) * coefficientField (H := EuclideanSpace ℂ (Fin n)) F t *
      matrixBaseField L t = tensorOperator (matrixOperatorMap n ((L t)ᴴ * L t)) (F t) := by
  change star (tensorOperator _ _) * tensorOperator _ _ * tensorOperator _ _ = _
  rw [← tensorOperator_star, ← tensorOperator_mul, ← tensorOperator_mul,
    star_one, one_mul, mul_one, mul_one]
  congr 1
  simp only [matrixOperatorMap_apply, ← Matrix.star_eq_conjTranspose, map_mul, map_star]

theorem norm_coefficientField_le_one {n : ℕ} (F : C(CircleSpace, Coeff n))
    (hF : ∀ t, ‖F t‖ ≤ 1) (t : CircleSpace) :
    ‖coefficientField (H := EuclideanSpace ℂ (Fin n)) F t‖ ≤ 1 := by
  change ‖tensorOperator (1 : Operator (EuclideanSpace ℂ (Fin n))) (F t)‖ ≤ 1
  exact (norm_tensorOperator_le _ _).trans (by
    calc
      ‖(1 : Operator (EuclideanSpace ℂ (Fin n)))‖ * ‖F t‖ ≤ 1 * 1 :=
        mul_le_mul ContinuousLinearMap.norm_id_le (hF t) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul _)

@[simp] theorem vectorization_inj {n : ℕ} {X Y : Coeff n} :
    vectorization X = vectorization Y ↔ X = Y := by
  constructor
  · intro h
    have he := congrArg (matrixAmplificationCoordinates n n) h
    rw [vectorization_coordinates, vectorization_coordinates] at he
    exact congrArg ofHS he
  · exact congrArg vectorization

theorem matrix_fibres_of_integral_interpolation {n : ℕ}
    (L F : C(CircleSpace, Coeff n))
    (hL : ∫ t, (L t)ᴴ * L t ∂circleMeasure = 1)
    (hF : ∀ t, ‖F t‖ ≤ 1) (X Y : Coeff n)
    (hN : ‖vectorization X‖ = ‖vectorization Y‖)
    (hI : (∫ t, tensorOperator (matrixOperatorMap n ((L t)ᴴ * L t)) (F t)
      ∂circleMeasure) (vectorization X) = vectorization Y) :
    ∀ᵐ t ∂circleMeasure,
      L t * Y = L t * X * (F t)ᵀ ∧ L t * X = L t * Y * (F t)ᴴᵀ := by
  have h := Compression.fibres_of_integral_interpolation
    (matrixBaseField L) (coefficientField (H := EuclideanSpace ℂ (Fin n)) F)
    (matrixBaseField_mass L hL) (norm_coefficientField_le_one F hF)
    (vectorization X) (vectorization Y) hN (by
      simpa only [matrixBaseField_sandwich] using hI)
  filter_upwards [h] with t ht
  obtain ⟨h1, h2⟩ := ht
  have he : (coefficientField (H := EuclideanSpace ℂ (Fin n)) F t).adjoint = coefficientField (H := EuclideanSpace ℂ (Fin n))
      ⟨fun t => (F t)ᴴ, F.continuous.star⟩ t := by
    change star (tensorOperator (1 : Operator (EuclideanSpace ℂ (Fin n))) (F t)) = _
    rw [← tensorOperator_star, star_one]
    rfl
  rw [he] at h2
  change tensorOperator (1 : Operator (EuclideanSpace ℂ (Fin n))) (F t)
      (tensorOperator (matrixOperatorMap n (L t)) (1 : Coeff n) (vectorization X)) =
      tensorOperator (matrixOperatorMap n (L t)) (1 : Coeff n) (vectorization Y) at h1
  change tensorOperator (1 : Operator (EuclideanSpace ℂ (Fin n))) (F t)ᴴ
      (tensorOperator (matrixOperatorMap n (L t)) (1 : Coeff n) (vectorization Y)) =
      tensorOperator (matrixOperatorMap n (L t)) (1 : Coeff n) (vectorization X) at h2
  have hone : (1 : Operator (EuclideanSpace ℂ (Fin n))) =
      Matrix.toEuclideanCLM (𝕜 := ℂ) (1 : Coeff n) := (map_one _).symm
  simp only [matrixOperatorMap_apply, hone, tensorOperator_vectorization,
    Matrix.transpose_one, mul_one, one_mul, vectorization_inj] at h1 h2
  exact ⟨h1.symm, h2.symm⟩

end CrouzeixHilbert

namespace CrouzeixHilbert.Boundary

def matrixDensityRoot {n : ℕ} (E : C(CircleSpace, Coeff n))
    (hE : ∀ t, (E t).PosSemidef) : C(CircleSpace, Coeff n) :=
  ⟨fun t => CFC.sqrt (E t),
    CFC.continuousOn_sqrt.comp_continuous E.continuous (fun t => (hE t).nonneg)⟩

@[simp] theorem matrixDensityRoot_star_mul {n : ℕ} (E : C(CircleSpace, Coeff n))
    (hE : ∀ t, (E t).PosSemidef) (t : CircleSpace) :
    (matrixDensityRoot E hE t)ᴴ * matrixDensityRoot E hE t = E t := by
  change star (CFC.sqrt (E t)) * CFC.sqrt (E t) = _
  rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)).star_eq,
    CFC.sqrt_mul_sqrt_self _ (hE t).nonneg]

theorem densityLp_ordered {n : ℕ} (E F : C(CircleSpace, Coeff n))
    (hE : ∀ t, (E t).PosSemidef) (hmass : ∫ t, E t ∂circleMeasure = 1)
    (hF : ∀ t, ‖F t‖ ≤ 1) (X Y : Coeff n)
    (hN : ‖vectorization X‖ = ‖vectorization Y‖)
    (hI : (∫ t, tensorOperator (matrixOperatorMap n (E t)) (F t)
      ∂circleMeasure) (vectorization X) = vectorization Y) :
    ∀ᵐ t ∂circleMeasure,
      ofHS (densityLp E X X t) = (F t)ᴴ * ofHS (densityLp E X Y t) ∧
      ofHS (densityLp E X Y t) = F t * ofHS (densityLp E X X t) ∧
      ofHS (densityLp E Y Y t) = ofHS (densityLp E X Y t) * (F t)ᴴ := by
  let L := matrixDensityRoot E hE
  have hf := matrix_fibres_of_integral_interpolation L F
    (by simpa only [L, matrixDensityRoot_star_mul] using hmass) hF X Y hN
    (by simpa only [L, matrixDensityRoot_star_mul] using hI)
  filter_upwards [hf, densityLp_apply_ae E X X, densityLp_apply_ae E X Y,
    densityLp_apply_ae E Y Y] with t ht hp hr hq
  simp only [hp, hq, hr, ofHS_toHS]
  have hL : (L t)ᴴ * L t = E t := matrixDensityRoot_star_mul E hE t
  rw [← hL, weightedPartialTrace_factor, weightedPartialTrace_factor,
    weightedPartialTrace_factor]
  exact crossPartialTrace_ordered (L t * X) (L t * Y) (F t) ht.1 ht.2

theorem matrixMean_cross_zero {n : ℕ} (E : C(CircleSpace, Coeff n))
    (hmass : ∫ t, E t ∂circleMeasure = 1) (X Y : Coeff n) (hXY : Xᴴ * Y = 0) :
    matrixMean (densityLp E X Y) = 0 := by
  rw [matrixMean_densityLp_mass_one E hmass, hXY, Matrix.transpose_zero]

theorem trace_matrixMean_self_one {n : ℕ} (E : C(CircleSpace, Coeff n))
    (hmass : ∫ t, E t ∂circleMeasure = 1) (X : Coeff n)
    (hX : ‖vectorization X‖ = 1) :
    (matrixMean (densityLp E X X)).trace = 1 := by
  rw [matrixMean_densityLp_mass_one E hmass, Matrix.trace_transpose,
    ← inner_vectorization, inner_self_eq_norm_sq_to_K, hX]
  norm_num

end CrouzeixHilbert.Boundary

end

end OAI
