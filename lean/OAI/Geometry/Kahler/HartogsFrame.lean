import OAI.Geometry.Kahler.HartogsErrorBounds

namespace OAI

open scoped ContDiff
open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
namespace PinchedHartogs
open PlaneAlgebra PlaneAlgebra.MatrixAlgebra PlaneAlgebra.TensorAlgebra Matrix

def normalIndexEquiv : Index ≃ Fin 3 := Equiv.ofBijective normalIndex (by
  constructor
  · intro a b hab
    cases a <;> cases b
    · rfl
    · rename_i b; fin_cases b <;> simp [normalIndex] at hab
    · rename_i a; fin_cases a <;> simp [normalIndex] at hab
    · rename_i a b
      exact congrArg some (Fin.castSucc_injective _ hab)
  · intro a
    fin_cases a
    · exact ⟨some 0, rfl⟩
    · exact ⟨some 1, rfl⟩
    · exact ⟨none, rfl⟩)

lemma sum_normalIndex (f : Fin 3 → ℂ) : (∑ i, f i) = ∑ a : Index, f (normalIndex a) :=
  (normalIndexEquiv.sum_comp f).symm

def normalFrameEquiv (r : ℝ) (hr : r ≠ 0) : FullVector ≃ₗ[ℂ] Ambient :=
  (LinearEquiv.piCongrRight (fun a : Index => LinearEquiv.smulOfNeZero ℂ ℂ
    (verticalScale r a : ℂ) (by cases a <;> simp [verticalScale, hr]))).trans
      ((LinearEquiv.funCongrLeft ℂ ℂ normalIndexEquiv).symm.trans coordinateLinearEquiv.symm)

lemma normalFrame_coordinates (r : ℝ) (hr : r ≠ 0) (u : FullVector) (a : Index) :
    coordinates (normalFrameEquiv r hr u) (normalIndex a) = (verticalScale r a : ℂ) * u a := by
  change coordinateLinearEquiv (normalFrameEquiv r hr u) (normalIndex a) = _
  simp only [normalFrameEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  change (verticalScale r (normalIndexEquiv.symm (normalIndexEquiv a)) : ℂ) *
    u (normalIndexEquiv.symm (normalIndexEquiv a)) = _
  rw [Equiv.symm_apply_apply]

lemma tensorValue_normalFrame (R : CurvatureTensor) (r : ℝ) (hr : r ≠ 0) (u v w y : FullVector) :
    tensorValue R (normalFrameEquiv r hr u) (normalFrameEquiv r hr v)
      (normalFrameEquiv r hr w) (normalFrameEquiv r hr y) =
      eval (pullTensor (verticalScale r) (fun a b c d => R (normalIndex a) (normalIndex b) (normalIndex c) (normalIndex d))) u v w y := by
  rw [eval_pull]
  simp only [tensorValue, eval, Fintype.sum_prod_type]
  simp_rw [sum_normalIndex, normalFrame_coordinates]
  rfl

lemma hermitianValue_normalFrame (A : CMatrix) (r : ℝ) (hr : r ≠ 0) (u v : FullVector) :
    hermitianValue A (normalFrameEquiv r hr u) (normalFrameEquiv r hr v) =
      pairValue (pullMatrix (verticalScale r) (fun a b => A (normalIndex a) (normalIndex b))) u v := by
  erw [pairValue_pull]
  simp only [hermitianValue, pairValue, dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply]
  simp_rw [sum_normalIndex, normalFrame_coordinates]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  simp only [pullVector]
  ring

lemma normalPotential_frame_metric {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (lam : ℝ) (w : ℂ) (hn : normalLogWeight f w (0,w) < 0) :
    pullMatrix (verticalScale ((Real.sqrt (barrierQ (normalLogWeight f w (0,w))))⁻¹))
        (fun a b => complexHessian (normalPotential f lam w) (0,w) (normalIndex a) (normalIndex b)) =
      block (horizontalMetric (baseHessian f 0) lam (barrierX (normalLogWeight f w (0,w)))) 1 := by
  rw [normalPotential_hessian_block hf lam w hn, complex_horizontalMetric]
  have hs := (sqrt_normalization (barrierQ (normalLogWeight f w (0,w))) (barrierQ_positive hn)).1
  ext a b
  cases a <;> cases b <;> simp only [pullMatrix, verticalScale, normalIndex]
  · simpa [block3, block, pow_two] using hs
  · rename_i b; fin_cases b <;> simp [block3, block]
  · rename_i a; fin_cases a <;> simp [block3, block]
  · rename_i a b; fin_cases a <;> fin_cases b <;> simp [block3, block]

lemma normalPotential_sectional {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (lam : ℝ) (w : ℂ) (hn : normalLogWeight f w (0,w) < 0) (u v : FullVector) :
    sectional (complexHessian (normalPotential f lam w)) (0,w)
      (normalFrameEquiv ((Real.sqrt (barrierQ (normalLogWeight f w (0,w))))⁻¹)
        (inv_ne_zero (Real.sqrt_pos.mpr (barrierQ_positive hn)).ne') u)
      (normalFrameEquiv ((Real.sqrt (barrierQ (normalLogWeight f w (0,w))))⁻¹)
        (inv_ne_zero (Real.sqrt_pos.mpr (barrierQ_positive hn)).ne') v) =
    H (normalCurvature f lam w) u v /
      (2*metricArea (horizontalMetric (baseHessian f 0) lam (barrierX (normalLogWeight f w (0,w)))) u v) := by
  simp only [sectional, tensorValue_normalFrame, normalCurvature, H,
    realArea, hermitianValue_normalFrame, normalPotential_frame_metric hf lam w hn,
    metricArea, qValue]

def metricErrorConstant (c C : ℝ) : ℝ := 9*(C+4*C^2/c)
def metricThreshold (c C : ℝ) : ℝ := pinchingThreshold c C (162*metricErrorConstant c C)

lemma metricThreshold_pos {c C : ℝ} (hc : 0 < c) (hC : c ≤ C) : 0 < metricThreshold c C := by
  exact lt_of_lt_of_le (show 0 < C+1 by linarith) (le_max_left _ _)

lemma normalPotentials_uniform_pinching {c C lam : ℝ} (hc : 0 < c) (hC : c ≤ C)
    (hlam : metricThreshold c C ≤ lam) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧
      ∀ (f : Base → ℝ) (hf : ContDiffAt ℝ ∞ f 0),
      (∀ u, c * euclidean.q u ≤ (form (baseHessian f 0)
        (baseHessian_isHermitian (hf.of_le (WithTop.coe_le_coe.mpr le_top)))).q u) →
      (∀ u, (form (baseHessian f 0)
        (baseHessian_isHermitian (hf.of_le (WithTop.coe_le_coe.mpr le_top)))).q u ≤ C * euclidean.q u) →
      (∀ i j k : Fin 2, ‖liftedThird f (0,0) i.castSucc j.castSucc k.castSucc‖ ≤ C) →
      (∀ i j k l : Fin 2, ‖liftedFourth f (0,0) i.castSucc j.castSucc k.castSucc l.castSucc‖ ≤ C) →
      ∀ w : ℂ, normalLogWeight f w (0,w) < 0 →
      ∀ u v : Ambient, LinearIndependent ℝ ![u,v] →
        -b ≤ sectional (complexHessian (normalPotential f lam w)) (0,w) u v ∧
          sectional (complexHessian (normalPotential f lam w)) (0,w) u v ≤ -a := by
  have hCp : 0 ≤ C := hc.le.trans hC
  have he : 0 ≤ metricErrorConstant c C := by unfold metricErrorConstant; positivity
  have hlp : 0 < lam := (metricThreshold_pos hc hC).trans_le hlam
  obtain ⟨a,b,ha,hab,hbound⟩ := curvatureModel_uniform_pinching hc hC he hlam
  refine ⟨a,b,ha,hab,?_⟩
  intro f hf hl hu hJ hB w hn u v hind
  let x := barrierX (normalLogWeight f w (0,w))
  let q := barrierQ (normalLogWeight f w (0,w))
  have hx : 0 ≤ x := (barrierX_positive hn).le
  have hH := baseHessian_isHermitian (hf.of_le (m := 2) (WithTop.coe_le_coe.mpr le_top))
  have hG : (horizontalMetric (baseHessian f 0) lam x).det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp (positive_horizontalMetric hc hlp hx _ hH hl).isUnit)
  let L := normalFrameEquiv ((Real.sqrt q)⁻¹) (inv_ne_zero (Real.sqrt_pos.mpr (barrierQ_positive hn)).ne')
  have hi : LinearIndependent ℝ ![L.symm u,L.symm v] := by
    convert hind.map' (L.symm.restrictScalars ℝ).toLinearMap
      (LinearMap.ker_eq_bot_of_injective (L.symm.restrictScalars ℝ).injective) using 1
    all_goals first | rfl | (ext i; fin_cases i <;> rfl)
  have hbnd := normalErrors_bounds hf hc hC hlp hl hu hJ hB w hn
  have hs := normalError_symmetries hf lam w hn
  have hbd := hbound x hx (baseHessian f 0) hH hl hu
    (horizontalPart 4 (normalError f lam w)) (horizontalPart 3 (normalError f lam w))
    (horizontalPart_symmetries 4 _ hs) (horizontalPart_symmetries 3 _ hs)
    (horizontalPart_supported 4 _) (horizontalPart_supported 3 _) hbnd.1 hbnd.2
    (L.symm u) (L.symm v) hi
  rw [← normalCurvature_model hf lam w hn hG] at hbd
  have heq := normalPotential_sectional hf lam w hn (L.symm u) (L.symm v)
  change sectional _ _ (L (L.symm u)) (L (L.symm v)) = _ at heq
  rw [L.apply_symm_apply, L.apply_symm_apply] at heq
  rwa [heq]

end PinchedHartogs

end

end OAI
