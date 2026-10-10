import Mathlib
import OAI.Analysis.Conductivity.Geometry.ExtendedCollar
import OAI.Analysis.Conductivity.Geometry.TorusFaceIntegration
import OAI.Analysis.Conductivity.Fourier.TorusPoissonContinuous

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus Matrix
open scoped Matrix.Norms.Elementwise

def sourceFaceAngles (i j : Fin 4) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![x 0,2*Real.pi*faceRayAngle 1 i (x 1),
    2*Real.pi*faceRayAngle sourceRadialWidth j (x 2)]

def sourceFaceAngleMatrix (i j : Fin 4) (x : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal ![1,2*Real.pi*faceRayDensity 1 i (x 1),
    2*Real.pi*faceRayDensity sourceRadialWidth j (x 2)]

lemma sourceFaceAngles_torus (i j : Fin 4) (x : Fin 3 → ℝ) :
    torusAngles (sourceFaceAngles i j x)=
      ![((faceRayAngle 1 i (x 1):ℝ):UnitAddCircle),
        ((faceRayAngle sourceRadialWidth j (x 2):ℝ):UnitAddCircle)] := by
  ext k
  fin_cases k <;> simp [torusAngles,sourceFaceAngles,Real.pi_ne_zero]

lemma sourceFaceAngles_hasFDeriv (i j : Fin 4) (x : Fin 3 → ℝ) :
    HasFDerivAt (sourceFaceAngles i j)
      (Matrix.toLin' (sourceFaceAngleMatrix i j x)).toContinuousLinearMap x := by
  have h1 := ((hasDerivAt_faceRayAngle 1 i (x 1)).comp_hasFDerivAt x
    (hasFDerivAt_apply (𝕜:=ℝ) 1 x)).const_mul (2*Real.pi)
  have h2 := ((hasDerivAt_faceRayAngle sourceRadialWidth j (x 2)).comp_hasFDerivAt x
    (hasFDerivAt_apply (𝕜:=ℝ) 2 x)).const_mul (2*Real.pi)
  have hcoord (k : Fin 3) : HasFDerivAt (fun y => sourceFaceAngles i j y k)
      ((ContinuousLinearMap.proj k : (Fin 3 → ℝ) →L[ℝ] ℝ).comp
        (Matrix.toLin' (sourceFaceAngleMatrix i j x)).toContinuousLinearMap) x := by
    fin_cases k
    · convert! hasFDerivAt_apply (𝕜:=ℝ) (0:Fin 3) x using 1
      ext v
      simp [sourceFaceAngleMatrix,Matrix.toLin'_apply,Matrix.mulVec_diagonal]
    · convert! h1 using 1
      ext v
      simp [sourceFaceAngleMatrix,Matrix.toLin'_apply,Matrix.mulVec_diagonal]
      ring
    · convert! h2 using 1
      ext v
      simp [sourceFaceAngleMatrix,Matrix.toLin'_apply,Matrix.mulVec_diagonal]
      ring
  convert! hasFDerivAt_pi.mpr hcoord using 1

lemma sourceFaceAngles_physical (i j : Fin 4) {x : Fin 3 → ℝ}
    (ha : |x 1|≤1) (hb : |x 2|≤1) :
    sourceAngularCollar (x 0) (torusAngles (sourceFaceAngles i j x))=
      sourceCollarPiece i j x := by
  rw [sourceFaceAngles_torus,sourceAngular_face _ _ _ _ _ ha hb]
  congr 1
  ext k
  fin_cases k <;> rfl

lemma continuous_sourceCollarJacobian (i j : Fin 4) : Continuous (sourceCollarJacobian i j) := by
  unfold sourceCollarJacobian sourceCollarRadius squareFace
  fun_prop

lemma continuous_sourceFaceAngleMatrix (i j : Fin 4) : Continuous (sourceFaceAngleMatrix i j) := by
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  by_cases hab : a=b
  · subst b
    fin_cases a <;> simp only [sourceFaceAngleMatrix,Matrix.diagonal_apply_eq]
    · exact continuous_const
    · exact continuous_const.mul ((continuous_faceRayDensity 1 i).comp (continuous_apply 1))
    · exact continuous_const.mul ((continuous_faceRayDensity sourceRadialWidth j).comp (continuous_apply 2))
  · simp only [sourceFaceAngleMatrix,Matrix.diagonal_apply_ne _ hab]
    exact continuous_const

lemma sourceCollarJacobian_extended_ne_zero (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100)) :
    (sourceCollarJacobian i j x).det≠0 := by
  have h := sourceExtended_jacobian_lower i j (le_refl _) (le_refl _) hx
  rw [sourceCollarDerivative_det,←sourceCollarJacobian_det] at h
  exact abs_pos.mp (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/100) h)

def sourceCartesianGradientMatrix (i j : Fin 4) (x : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (sourceCollarJacobian i j x)ᵀ⁻¹*sourceFaceAngleMatrix i j x

lemma sourceCartesianGradient_chain (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100)) (v : Fin 3 → ℝ) :
    (sourceCollarJacobian i j x)ᵀ *ᵥ (sourceCartesianGradientMatrix i j x *ᵥ v)=
      sourceFaceAngleMatrix i j x *ᵥ v := by
  rw [sourceCartesianGradientMatrix,←Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (by
      rw [Matrix.det_transpose]
      exact sourceCollarJacobian_extended_ne_zero i j hx)),Matrix.one_mulVec]

lemma continuousOn_sourceCartesianGradientMatrix (i j : Fin 4) :
    ContinuousOn (sourceCartesianGradientMatrix i j)
      (sourceExtendedBox (-(1:ℝ)/100) (1/100)) := by
  intro x hx
  have hi : ContinuousAt (fun x => (sourceCollarJacobian i j x)ᵀ⁻¹) x :=
    (continuousAt_matrix_inv _ (by
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ (by
        rw [Matrix.det_transpose]
        exact sourceCollarJacobian_extended_ne_zero i j hx))).comp
          (continuous_sourceCollarJacobian i j).matrix_transpose.continuousAt
  exact (hi.mul (continuous_sourceFaceAngleMatrix i j).continuousAt).continuousWithinAt

lemma sourceCartesianGradient_uniform_bound : ∃ C : ℝ,0<C ∧
    ∀ (i j : Fin 4) (x : Fin 3 → ℝ),x∈sourceExtendedBox (-(1:ℝ)/100) (1/100) →
      ∀ a b : Fin 3,|sourceCartesianGradientMatrix i j x a b|≤C := by
  have hb (i j : Fin 4) : ∃ C : ℝ,∀ x∈sourceExtendedBox (-(1:ℝ)/100) (1/100),
      ‖sourceCartesianGradientMatrix i j x‖≤C :=
    (isCompact_Icc : IsCompact (sourceExtendedBox (-(1:ℝ)/100) (1/100))).exists_bound_of_continuousOn
      (continuousOn_sourceCartesianGradientMatrix i j)
  choose C hC using hb
  refine ⟨1+∑ i : Fin 4,∑ j : Fin 4,|C i j|,by positivity,?_⟩
  intro i j x hx a b
  have hentry : |sourceCartesianGradientMatrix i j x a b|≤C i j := by
    simpa only [Real.norm_eq_abs] using
      (norm_le_pi_norm (sourceCartesianGradientMatrix i j x a) b).trans
        ((norm_le_pi_norm (sourceCartesianGradientMatrix i j x) a).trans (hC i j x hx))
  have hsum : |C i j|≤∑ i : Fin 4,∑ j : Fin 4,|C i j| :=
    (Finset.single_le_sum (fun k _ => abs_nonneg (C i k)) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => abs_nonneg (C k l)))
        (Finset.mem_univ i))
  linarith [le_abs_self (C i j)]

end ScalarConductivity

end

end OAI
