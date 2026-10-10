import Mathlib
import OAI.Analysis.Crouzeix.ResolventBounds

namespace OAI

/-! Matrix Contours. -/

noncomputable section

open scoped TensorProduct Matrix.Norms.L2Operator InnerProductSpace Topology

open Set Filter

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

local instance matrixContourOperatorRealNormedSpace (m : ℕ) :
    NormedSpace ℝ (Operator (Amplification H m)) :=
  NormedSpace.restrictScalars ℝ ℂ _

def tensorCoefficientCLM (A : Operator H) (m : ℕ) :
    Coeff m →L[ℂ] Operator (Amplification H m) := by
  let L : Coeff m →ₗ[ℂ] Operator (Amplification H m) :=
    { toFun := fun B => tensorOperator A B
      map_add' := by
        intro B C
        apply ContinuousLinearMap.ext
        intro v
        refine UniformSpace.Completion.induction_on v
          (isClosed_eq (tensorOperator A (B + C)).continuous
            ((tensorOperator A B).continuous.add (tensorOperator A C).continuous)) ?_
        intro a
        simp only [tensorOperator, map_add, TensorProduct.mapL_add_right,
          ContinuousLinearMap.completion_apply_coe, add_apply,
          UniformSpace.Completion.coe_add]
      map_smul' := by
        intro c B
        apply ContinuousLinearMap.ext
        intro v
        refine UniformSpace.Completion.induction_on v
          (isClosed_eq (tensorOperator A (c • B)).continuous
            ((tensorOperator A B).continuous.const_smul c)) ?_
        intro a
        simp only [tensorOperator, map_smul, TensorProduct.mapL_smul_right,
          ContinuousLinearMap.completion_apply_coe, smul_apply,
          UniformSpace.Completion.coe_smul, RingHom.id_apply] }
  exact L.mkContinuous ‖A‖ (fun B => norm_tensorOperator_le A B)

@[simp]
theorem tensorCoefficientCLM_apply (A : Operator H) {m : ℕ} (B : Coeff m) :
    tensorCoefficientCLM A m B = tensorOperator A B := rfl

theorem sum_tensorOperator_entries (A : Operator H) {m : ℕ} (B : Coeff m) :
    (∑ i, ∑ j, tensorOperator (B i j • A) (Matrix.single i j 1)) = tensorOperator A B := by
  have hsum : (∑ i, ∑ j, B i j • Matrix.single i j (1 : ℂ)) = B := by
    simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using (Matrix.matrix_eq_sum_single B).symm
  calc
    _ = ∑ i, ∑ j, B i j • tensorCoefficientCLM A m (Matrix.single i j 1) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact map_smul (tensorOperatorCLM (Matrix.single i j 1)) (B i j) A
    _ = tensorCoefficientCLM A m (∑ i, ∑ j, B i j • Matrix.single i j 1) := by
      simp only [map_sum, map_smul]
    _ = tensorOperator A B := by rw [hsum]; rfl

theorem matrixContourEval_eq_integral [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) {m : ℕ} {F : ℂ → Coeff m}
    (hF : ContinuousOn F Γ.toSmoothContour.trace) :
    matrixContourEval A Γ.toSmoothContour F =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
        ∫ t in (0 : ℝ)..1, tensorOperator (contourKernel A Γ.toSmoothContour t) (F (Γ.path t)) := by
  let k := contourKernel A Γ.toSmoothContour
  let g (i j : Fin m) (t : ℝ) := F (Γ.path t) i j • k t
  let T (i j : Fin m) := tensorOperatorCLM (H := H) (Matrix.single i j 1)
  have hg (i j : Fin m) : ContinuousOn (g i j) (Icc (0 : ℝ) 1) :=
    (((matrixEntryCLM i j).continuous.comp_continuousOn hF).comp
      Γ.smooth.continuous.continuousOn (fun t ht => mem_image_of_mem _ ht)).smul
      (continuousOn_contourKernel A Γ)
  have hi (i j : Fin m) : IntervalIntegrable (g i j) MeasureTheory.volume (0 : ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le zero_le_one] using hg i j
  have hTi (i j : Fin m) :
      IntervalIntegrable (fun t => T i j (g i j t)) MeasureTheory.volume (0 : ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le zero_le_one, Function.comp_def] using!
      (T i j).continuous.comp_continuousOn (hg i j)
  have hTiSum (i : Fin m) : IntervalIntegrable (fun t => ∑ j, T i j (g i j t))
      MeasureTheory.volume (0 : ℝ) 1 := by
    have hcc : ContinuousOn (fun t => ∑ j, T i j (g i j t)) (Icc (0 : ℝ) 1) := by
      apply continuousOn_finsetSum
      intro j _
      exact (T i j).continuous.comp_continuousOn (hg i j)
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le zero_le_one] using! hcc
  have hsum : (∑ i, ∑ j, T i j (∫ t in (0 : ℝ)..1, g i j t)) =
      ∫ t in (0 : ℝ)..1, ∑ i, ∑ j, T i j (g i j t) := by
    simp_rw [← ContinuousLinearMap.intervalIntegral_comp_comm _ (hi _ _)]
    rw [intervalIntegral.integral_finsetSum (fun i _ => hTiSum i)]
    apply Finset.sum_congr rfl
    intro i _
    exact (intervalIntegral.integral_finsetSum (fun j _ => hTi i j)).symm
  calc
    _ = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
        ∑ i, ∑ j, T i j (∫ t in (0 : ℝ)..1, g i j t) := by
      unfold matrixContourEval
      simp only [contourEval_eq_kernel, ← tensorOperatorCLM_apply, map_smul,
        Finset.smul_sum, T, g, k]
    _ = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
        ∫ t in (0 : ℝ)..1, ∑ i, ∑ j, T i j (g i j t) := by rw [hsum]
    _ = _ := by
      congr 1
      apply intervalIntegral.integral_congr
      intro t _
      exact sum_tensorOperator_entries (k t) (F (Γ.path t))

def SmoothContour.arcLength (Γ : SmoothContour) : ℝ :=
  ∫ t in (0 : ℝ)..1, ‖deriv Γ.path t‖

theorem SmoothContour.arcLength_nonneg (Γ : SmoothContour) : 0 ≤ Γ.arcLength :=
  intervalIntegral.integral_nonneg zero_le_one (fun _ _ => norm_nonneg _)

theorem norm_matrixContourEval_le [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) {m : ℕ} {F : ℂ → Coeff m}
    (hF : ContinuousOn F Γ.toSmoothContour.trace) :
    ‖matrixContourEval A Γ.toSmoothContour F‖ ≤
      (Γ.toSmoothContour.arcLength / (2 * Real.pi)) *
        supNorm Γ.toSmoothContour.trace (fun z => Ring.inverse (algebraMap ℂ (Operator H) z - A)) *
        supNorm Γ.toSmoothContour.trace F := by
  let res := fun z => Ring.inverse (algebraMap ℂ (Operator H) z - A)
  let M := supNorm Γ.toSmoothContour.trace res
  let S := supNorm Γ.toSmoothContour.trace F
  have hr : ContinuousOn res Γ.toSmoothContour.trace :=
    (continuousOn_resolvent A).mono (by
      rintro z ⟨t, ht, rfl⟩
      exact (Γ.avoids t ht).2)
  have hbM := supNorm_bddAbove Γ.toSmoothContour.isCompact_trace hr
  have hbS := supNorm_bddAbove Γ.toSmoothContour.isCompact_trace hF
  have hm : 0 ≤ M := supNorm_nonneg hbM
  have hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖tensorOperator (contourKernel A Γ.toSmoothContour t) (F (Γ.path t))‖ ≤
        ‖deriv Γ.path t‖ * M * S := by
    intro t ht
    have htrace : Γ.path t ∈ Γ.toSmoothContour.trace := mem_image_of_mem _ ht
    calc
      _ ≤ ‖contourKernel A Γ.toSmoothContour t‖ * ‖F (Γ.path t)‖ := norm_tensorOperator_le _ _
      _ = (‖deriv Γ.path t‖ * ‖res (Γ.path t)‖) * ‖F (Γ.path t)‖ := by
        rw [contourKernel, norm_smul]
      _ ≤ (‖deriv Γ.path t‖ * M) * S :=
        mul_le_mul (mul_le_mul_of_nonneg_left (norm_le_supNorm hbM htrace) (norm_nonneg _))
          (norm_le_supNorm hbS htrace) (norm_nonneg _) (mul_nonneg (norm_nonneg _) hm)
  have hi : IntervalIntegrable (fun t => ‖deriv Γ.path t‖ * M * S)
      MeasureTheory.volume (0 : ℝ) 1 :=
    ((Γ.smooth.continuous_deriv_one.norm.mul_const M).mul_const S).intervalIntegrable _ _
  have hn := intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    (Filter.Eventually.of_forall (fun t ht => hbound t ⟨ht.1.le, ht.2⟩)) hi
  have hn' : ‖∫ t in (0 : ℝ)..1,
      tensorOperator (contourKernel A Γ.toSmoothContour t) (F (Γ.path t))‖ ≤
        Γ.toSmoothContour.arcLength * M * S := by
    simpa only [intervalIntegral.integral_mul_const, SmoothContour.arcLength] using hn
  have hc : ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹‖ = (2 * Real.pi)⁻¹ := by
    simp
  rw [matrixContourEval_eq_integral A Γ hF, norm_smul, hc]
  calc
    _ ≤ (2 * Real.pi)⁻¹ * (Γ.toSmoothContour.arcLength * M * S) :=
      mul_le_mul_of_nonneg_left hn' (inv_nonneg.mpr (by positivity))
    _ = (Γ.toSmoothContour.arcLength / (2 * Real.pi)) * M * S := by ring

theorem matrixContourEval_sub [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) {m : ℕ} {F G : ℂ → Coeff m}
    (hF : ContinuousOn F Γ.toSmoothContour.trace)
    (hG : ContinuousOn G Γ.toSmoothContour.trace) :
    matrixContourEval A Γ.toSmoothContour (F - G) =
      matrixContourEval A Γ.toSmoothContour F - matrixContourEval A Γ.toSmoothContour G := by
  have he (i j : Fin m) :
      contourEval A Γ.toSmoothContour (fun z => (F z - G z) i j) =
        contourEval A Γ.toSmoothContour (fun z => F z i j) -
          contourEval A Γ.toSmoothContour (fun z => G z i j) :=
    contourEval_sub A Γ ((matrixEntryCLM i j).continuous.comp_continuousOn hF)
      ((matrixEntryCLM i j).continuous.comp_continuousOn hG)
  simp only [matrixContourEval, Pi.sub_apply, he, ← tensorOperatorCLM_apply,
    map_sub, Finset.sum_sub_distrib]

theorem norm_matrixContourEval_sub_le [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (Γ : CalculusContour (numericalClosure A) U) {m : ℕ} {F G : ℂ → Coeff m}
    (hF : ContinuousOn F Γ.toSmoothContour.trace)
    (hG : ContinuousOn G Γ.toSmoothContour.trace) :
    ‖matrixContourEval A Γ.toSmoothContour F - matrixContourEval A Γ.toSmoothContour G‖ ≤
      (Γ.toSmoothContour.arcLength / (2 * Real.pi)) *
        supNorm Γ.toSmoothContour.trace (fun z => Ring.inverse (algebraMap ℂ (Operator H) z - A)) *
        supNorm Γ.toSmoothContour.trace (F - G) := by
  rw [← matrixContourEval_sub A Γ hF hG]
  exact norm_matrixContourEval_le A Γ (hF.sub hG)

end CrouzeixHilbert

end

end OAI
