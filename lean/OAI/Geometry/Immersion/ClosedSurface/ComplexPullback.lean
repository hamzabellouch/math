import OAI.Geometry.Immersion.ClosedSurface.TensorCoordinates

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseMean
open ClosedSurfaceR4.SmallModes (Base dx dy)
open ClosedSurfaceR4.QuadraticMean (realMode)
open ClosedSurfaceR4.RealModes (base_decomposition)

abbrev ComplexTensor := Fin 3 → ℂ

def complexEvaluate (A : ComplexTensor) (v w : Base) : ℂ :=
  A 0 * (v.1 : ℂ) * (w.1 : ℂ) +
    A 1 * ((v.1 : ℂ) * (w.2 : ℂ) + (v.2 : ℂ) * (w.1 : ℂ)) +
    A 2 * (v.2 : ℂ) * (w.2 : ℂ)



def complexPullback (J : Base →L[ℝ] Base) : ComplexTensor →L[ℂ] ComplexTensor :=
  LinearMap.toContinuousLinearMap {
    toFun := fun A i => complexEvaluate A (J (firstDirection i)) (J (secondDirection i))
    map_add' := by intro A B; ext i; simp only [complexEvaluate, Pi.add_apply]; ring
    map_smul' := by intro c A; ext i; simp only [complexEvaluate, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply]; ring }

def complexPullbackField (χ : Base → Base) (p : Base) : ComplexTensor →L[ℂ] ComplexTensor :=
  complexPullback (fderiv ℝ χ p)

lemma complexPullback_apply (J : Base →L[ℝ] Base) (A : ComplexTensor) (i : Fin 3) :
    complexPullback J A i = complexEvaluate A (J (firstDirection i)) (J (secondDirection i)) := rfl

lemma complexEvaluate_pullback (J : Base →L[ℝ] Base) (A : ComplexTensor) (v w : Base) :
    complexEvaluate (complexPullback J A) v w = complexEvaluate A (J v) (J w) := by
  have hv : J v = v.1 • J dx + v.2 • J dy := by
    conv_lhs => rw [base_decomposition v]
    simp only [map_add, map_smul]
  have hw : J w = w.1 • J dx + w.2 • J dy := by
    conv_lhs => rw [base_decomposition w]
    simp only [map_add, map_smul]
  rw [hv, hw]
  simp only [complexEvaluate, complexPullback_apply, firstDirection, secondDirection,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    Complex.ofReal_add, Complex.ofReal_mul]
  ring

lemma complexPullback_comp (J K : Base →L[ℝ] Base) (A : ComplexTensor) :
    complexPullback J (complexPullback K A) = complexPullback (K.comp J) A := by
  ext i
  rw [complexPullback_apply, complexEvaluate_pullback, complexPullback_apply]
  rfl

lemma complexPullback_id (A : ComplexTensor) :
    complexPullback (ContinuousLinearMap.id ℝ Base) A = A := by
  ext i
  fin_cases i <;> simp [complexPullback_apply, complexEvaluate, firstDirection,
    secondDirection, dx, dy]

lemma realPart_complexPullback (J : Base →L[ℝ] Base) (A : ComplexTensor) :
    ClosedSurfaceR4.QuadraticMean.realPart (complexPullback J A) = pullback J (ClosedSurfaceR4.QuadraticMean.realPart A) := by
  ext i
  change (complexEvaluate A _ _).re = evaluate (ClosedSurfaceR4.QuadraticMean.realPart A) _ _
  simp [complexEvaluate, evaluate, ClosedSurfaceR4.QuadraticMean.realPart, Complex.mul_re]

lemma realMode_complexPullback (J : Base →L[ℝ] Base) (A : ComplexTensor) (θ : ℝ) :
    realMode θ (complexPullback J A) = pullback J (realMode θ A) := by
  unfold realMode
  rw [← map_smul, realPart_complexPullback]

lemma complexPullbackField_inverse {χ e : Base → Base} {p : Base}
    (hχ : DifferentiableAt ℝ χ p) (he : DifferentiableAt ℝ e (χ p))
    (hinv : e ∘ χ =ᶠ[nhds p] id) (A : ComplexTensor) :
    complexPullbackField χ p (complexPullbackField e (χ p) A) = A := by
  unfold complexPullbackField
  rw [complexPullback_comp, ← fderiv_comp p he hχ,
    hinv.fderiv_eq, fderiv_id, complexPullback_id]



lemma oscillating_pullback_inverse {χ e : Base → Base} {p : Base}
    (hχ : DifferentiableAt ℝ χ p) (he : DifferentiableAt ℝ e (χ p))
    (hinv : e ∘ χ =ᶠ[nhds p] id) (A : ComplexTensor) (θ : ℝ) :
    pullbackField χ p (realMode θ (complexPullbackField e (χ p) A)) = realMode θ A := by
  change pullback (fderiv ℝ χ p) _ = _
  rw [← realMode_complexPullback]
  exact congrArg (realMode θ) (complexPullbackField_inverse hχ he hinv A)

end ClosedSurfaceR4.PhaseMean

namespace ClosedSurfaceR4.PhaseMean
open ClosedSurfaceR4.SmallModes (Base Field coordDeriv)

lemma contDiffOn_complexEvaluate {U : Set Base} {A : Base → ComplexTensor}
    {v w : Base → Base} (hA : ContDiffOn ℝ ∞ A U) (hv : ContDiffOn ℝ ∞ v U)
    (hw : ContDiffOn ℝ ∞ w U) :
    ContDiffOn ℝ ∞ (fun p => complexEvaluate (A p) (v p) (w p)) U := by
  have hvc := Complex.ofRealCLM.contDiff.comp_contDiffOn hv.fst
  have hvd := Complex.ofRealCLM.contDiff.comp_contDiffOn hv.snd
  have hwc := Complex.ofRealCLM.contDiff.comp_contDiffOn hw.fst
  have hwd := Complex.ofRealCLM.contDiff.comp_contDiffOn hw.snd
  have h0 := ((contDiffOn_pi.mp hA 0).mul hvc).mul hwc
  have h1 := (contDiffOn_pi.mp hA 1).mul ((hvc.mul hwd).add (hvd.mul hwc))
  have h2 := ((contDiffOn_pi.mp hA 2).mul hvd).mul hwd
  exact (h0.add h1).add h2

lemma contDiffOn_complexPullbackField_apply {U : Set Base} (hU : IsOpen U)
    {A : Base → ComplexTensor} {e : Base → Base}
    (hA : ContDiffOn ℝ ∞ A U) (he : ContDiffOn ℝ ∞ e U) :
    ContDiffOn ℝ ∞ (fun p => complexPullbackField e p (A p)) U := by
  apply contDiffOn_pi.mpr
  intro i
  exact contDiffOn_complexEvaluate hA
    (ClosedSurfaceR4.SmallModes.contDiffOn_coordDeriv_vector hU he (firstDirection i))
    (ClosedSurfaceR4.SmallModes.contDiffOn_coordDeriv_vector hU he (secondDirection i))


def coordinateTarget (e : Base → Base) (A : Base → ComplexTensor) : Base → ComplexTensor :=
  fun p => complexPullbackField e p (A (e p))

lemma contDiffOn_coordinateTarget {U V : Set Base} (hV : IsOpen V)
    {A : Base → ComplexTensor} {e : Base → Base}
    (hA : ContDiffOn ℝ ∞ A U) (he : ContDiffOn ℝ ∞ e V) (heU : Set.MapsTo e V U) :
    ContDiffOn ℝ ∞ (coordinateTarget e A) V :=
  contDiffOn_complexPullbackField_apply hV (hA.comp he heU) he

end ClosedSurfaceR4.PhaseMean

end

end OAI
