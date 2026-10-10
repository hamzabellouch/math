import Mathlib
import OAI.Analysis.Crouzeix.AngularMeasure
import OAI.Analysis.Crouzeix.PhysicalComparison

namespace OAI

/-! Physical Density. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace CrouzeixHilbert

open Boundary

namespace Conformal.ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U) (R : InteriorCollar U)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance physicalDensityOperatorRealNormedSpace (size : ℕ) :
    NormedSpace ℝ (Operator (Amplification H size)) :=
  NormedSpace.restrictScalars ℝ ℂ _

def operatorDensity (D : Operator H) (hD : spectralRadius ℂ D < 1) : C(CircleSpace, Operator H) :=
  ⟨fun t => C.angularJacobian R t • Disk.phi D (C.interiorAngle R t),
    (C.angularJacobian R).continuous.smul ((Disk.continuous_phi D hD).comp (C.interiorAngle R).continuous)⟩

lemma operatorDensity_nonneg (D : Operator H) (hD : spectralRadius ℂ D < 1)
    (hN : ‖D‖ ≤ 1) (t : CircleSpace) : 0 ≤ C.operatorDensity R D hD t := by
  have he : C.angularJacobian R t = ((C.angularJacobian R t).re : ℂ) := by
    apply Complex.ext <;> simp [(C.angularJacobian_real_nonneg R t).1]
  change 0 ≤ C.angularJacobian R t • Disk.phi D (C.interiorAngle R t)
  rw [he]
  exact smul_nonneg (by simpa using (C.angularJacobian_real_nonneg R t).2)
    (ContinuousLinearMap.nonneg_iff_isPositive.mpr (Disk.phi_isPositive D hN hD _))

lemma integral_operatorDensity (D : Operator H) (hD : spectralRadius ℂ D < 1)
    (hU : IsOpen U) (hc : Convex ℝ U) :
    (∫ t, C.operatorDensity R D hD t ∂circleMeasure) = 1 := by
  change (∫ t, C.angularJacobian R t • Disk.phi D (C.interiorAngle R t) ∂circleMeasure) = 1
  exact (C.integral_angularChange R hU hc ⟨Disk.phi D, Disk.continuous_phi D hD⟩).trans
    (Disk.integral_phi D hD)

lemma integral_operatorDensity_pullback (D : Operator H) (hD : spectralRadius ℂ D < 1)
    (hU : IsOpen U) (hc : Convex ℝ U) {m : ℕ} (F : C(CircleSpace, Coeff m)) :
    (∫ t, tensorOperator (C.operatorDensity R D hD t) (F (C.interiorAngle R t)) ∂circleMeasure) =
      ∫ t, tensorOperator (Disk.phi D t) (F t) ∂circleMeasure := by
  let V : C(CircleSpace, Operator (Amplification H m)) :=
    ⟨fun t => tensorOperator (Disk.phi D t) (F t),
      ((tensorBilinearCLM m).continuous.comp (Disk.continuous_phi D hD)).clm_apply F.continuous⟩
  have he (t : CircleSpace) : tensorOperator (C.operatorDensity R D hD t) (F (C.interiorAngle R t)) =
      C.angularJacobian R t • V (C.interiorAngle R t) := by
    change tensorOperator (C.angularJacobian R t • Disk.phi D (C.interiorAngle R t)) _ = _
    exact (tensorOperatorCLM _).map_smul _ _
  simp_rw [he]
  exact C.integral_angularChange R hU hc V

end Conformal.ExteriorCollar

def operatorToMatrix (n : ℕ) : Operator (EuclideanSpace ℂ (Fin n)) →L[ℂ] Coeff n :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).symm.toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv.toContinuousLinearMap

@[simp] lemma operatorToMatrix_apply {n : ℕ} (A : Operator (EuclideanSpace ℂ (Fin n))) :
    operatorToMatrix n A = (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm A := rfl

namespace Conformal.ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U) (R : InteriorCollar U)

def matrixDensity {n : ℕ} (D : Operator (EuclideanSpace ℂ (Fin n)))
    (hD : spectralRadius ℂ D < 1) : C(CircleSpace, Coeff n) :=
  ⟨fun t => operatorToMatrix n (C.operatorDensity R D hD t),
    (operatorToMatrix n).continuous.comp (C.operatorDensity R D hD).continuous⟩

lemma matrixDensity_posSemidef {n : ℕ} (D : Operator (EuclideanSpace ℂ (Fin n)))
    (hD : spectralRadius ℂ D < 1) (hN : ‖D‖ ≤ 1) (t : CircleSpace) :
    (C.matrixDensity R D hD t).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  exact map_nonneg (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).symm
    (C.operatorDensity_nonneg R D hD hN t)

lemma integral_matrixDensity {n : ℕ} (D : Operator (EuclideanSpace ℂ (Fin n)))
    (hD : spectralRadius ℂ D < 1) (hU : IsOpen U) (hc : Convex ℝ U) :
    (∫ t, C.matrixDensity R D hD t ∂circleMeasure) = 1 := by
  let : ContinuousSMul ℂ (EuclideanSpace ℂ (Fin n)) := IsBoundedSMul.continuousSMul
  let : CompleteSpace (Operator (EuclideanSpace ℂ (Fin n))) :=
    ContinuousLinearMap.instCompleteSpace
  have hi : Integrable (C.operatorDensity R D hD) circleMeasure :=
    (C.operatorDensity R D hD).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change (∫ t, operatorToMatrix n (C.operatorDensity R D hD t) ∂circleMeasure) = 1
  rw [(operatorToMatrix n).integral_comp_comm hi, C.integral_operatorDensity R D hD hU hc]
  exact map_one (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).symm

lemma tensorIntegral_matrixDensity_pullback {n : ℕ} (D : Operator (EuclideanSpace ℂ (Fin n)))
    (hD : spectralRadius ℂ D < 1) (hU : IsOpen U) (hc : Convex ℝ U)
    (F : C(CircleSpace, Coeff n)) :
    Boundary.tensorIntegral (C.matrixDensity R D hD) (F.comp (C.interiorAngle R)) =
      ∫ t, tensorOperator (Disk.phi D t) (F t) ∂circleMeasure := by
  change (∫ t, tensorOperator (Matrix.toEuclideanCLM (𝕜 := ℂ) (C.matrixDensity R D hD t)) (F (C.interiorAngle R t)) ∂circleMeasure) = _
  simp only [matrixDensity, ContinuousMap.coe_mk, operatorToMatrix_apply, StarAlgEquiv.apply_symm_apply]
  exact C.integral_operatorDensity_pullback R D hD hU hc F

end Conformal.ExteriorCollar

end CrouzeixHilbert

end

end OAI
