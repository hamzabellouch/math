import OAI.Geometry.Immersion.ClosedSurface.TensorCoordinates
import OAI.Geometry.Immersion.ClosedSurface.CrossModes

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.QuadraticMean

lemma zeroPair_add_left {n : ℕ} (A B C : CVec n) :
    zeroPair (A + B) C = zeroPair A C + zeroPair B C := by
  simp [zeroPair, add_dotProduct, add_div]

lemma zeroPair_add_right {n : ℕ} (A B C : CVec n) :
    zeroPair A (B + C) = zeroPair A B + zeroPair A C := by
  have hc : conjugate (B + C) = conjugate B + conjugate C := by
    ext i; simp [conjugate]
  simp [zeroPair, hc, dotProduct_add, add_div]

lemma zeroPair_smul_left {n : ℕ} (a : ℝ) (A B : CVec n) :
    zeroPair (a • A) B = a * zeroPair A B := by
  simp [zeroPair, smul_dotProduct, mul_div_assoc]

lemma zeroPair_smul_right {n : ℕ} (a : ℝ) (A B : CVec n) :
    zeroPair A (a • B) = a * zeroPair A B := by
  have hc : conjugate (a • B) = a • conjugate B := by
    ext i; simp [conjugate]
  simp [zeroPair, hc, dotProduct_smul, mul_div_assoc]

lemma zeroPair_comm {n : ℕ} (A B : CVec n) : zeroPair A B = zeroPair B A := by
  unfold zeroPair dotProduct conjugate
  simp only [Complex.re_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

end ClosedSurfaceR4.QuadraticMean

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseMean
open ClosedSurfaceR4.QuadraticMean (zeroPair derivativeAmplitude zeroPair_add_left
  zeroPair_add_right zeroPair_smul_left zeroPair_smul_right zeroPair_comm)

lemma gradientAmplitude_base_decomposition {n : ℕ} (τ : ℝ) (Z : Field n) (v p : Base) :
    gradientAmplitude τ Z v p = v.1 • gradientAmplitude τ Z dx p +
      v.2 • gradientAmplitude τ Z dy p := by
  unfold gradientAmplitude
  have hd : coordDeriv v Z p = v.1 • coordDeriv dx Z p + v.2 • coordDeriv dy Z p := by
    unfold coordDeriv
    conv_lhs => rw [base_decomposition v]
    simp only [map_add, map_smul]
  rw [hd]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, dx, dy, Complex.ofReal_one, Complex.ofReal_zero,
    mul_one, mul_zero, zero_smul, add_zero, smul_add, smul_eq_mul, Complex.real_smul]
  ring

lemma evaluate_phaseZeroTensor {n : ℕ} (τ : ℝ) (Z : Field n) (p v w : Base) :
    evaluate (phaseZeroTensor τ Prod.fst Z p) v w =
      zeroPair (gradientAmplitude τ Z v p) (gradientAmplitude τ Z w p) := by
  rw [gradientAmplitude_base_decomposition τ Z v p, gradientAmplitude_base_decomposition τ Z w p]
  simp only [zeroPair_add_left, zeroPair_add_right, zeroPair_smul_left, zeroPair_smul_right]
  unfold evaluate phaseZeroTensor
  simp only [← gradientAmplitude_eq, firstDirection, secondDirection, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  rw [zeroPair_comm (gradientAmplitude τ Z dy p) (gradientAmplitude τ Z dx p)]
  ring

lemma derivativeAmplitude_coordinate {n : ℕ} {Z : Field n} {χ : Base → Base} {p : Base}
    (hZ : DifferentiableAt ℝ Z (χ p)) (hχ : DifferentiableAt ℝ χ p) (τ : ℝ) (v : Base) :
    derivativeAmplitude τ (fun p => (χ p).1) (Z ∘ χ) v p =
      gradientAmplitude τ Z (fderiv ℝ χ p v) (χ p) := by
  have hfst : DifferentiableAt ℝ (Prod.fst : Base → ℝ) (χ p) := differentiableAt_fst
  change derivativeAmplitude τ (Prod.fst ∘ χ) (Z ∘ χ) v p = _
  simp only [derivativeAmplitude, gradientAmplitude, coordDeriv,
    fderiv_comp p hZ hχ, fderiv_comp p hfst hχ, fderiv_fst,
    ContinuousLinearMap.comp_apply]
  rfl

lemma phaseZeroTensor_coordinate {n : ℕ} {Z : Field n} {χ : Base → Base} {p : Base}
    (hZ : DifferentiableAt ℝ Z (χ p)) (hχ : DifferentiableAt ℝ χ p) (τ : ℝ) :
    phaseZeroTensor τ (fun p => (χ p).1) (Z ∘ χ) p =
      pullbackField χ p (phaseZeroTensor τ Prod.fst Z (χ p)) := by
  ext i
  change zeroPair (derivativeAmplitude τ (fun p => (χ p).1) (Z ∘ χ) (firstDirection i) p)
    (derivativeAmplitude τ (fun p => (χ p).1) (Z ∘ χ) (secondDirection i) p) =
    evaluate (phaseZeroTensor τ Prod.fst Z (χ p))
      (fderiv ℝ χ p (firstDirection i)) (fderiv ℝ χ p (secondDirection i))
  rw [derivativeAmplitude_coordinate hZ hχ, derivativeAmplitude_coordinate hZ hχ,
    evaluate_phaseZeroTensor]




lemma freePhase_zeroTensor {F : RField 4} {V : Set Base} (h : RealModeDomain F V)
    {δ τ : ℝ} (hδ : δ ≠ 0) (hτ : τ ≠ 0) (b : Base → ℝ) (q : ℕ)
    {p : Base} (hp : p ∈ V) :
    phaseZeroTensor τ Prod.fst
      (modeApprox τ (fun p => complexify (F p)) (freeSeed δ τ b F) (fun _ => 0) q) p =
      δ ^ 2 • (fun i => b p ^ 2 * (firstDirection i).1 * (secondDirection i).1) +
      δ ^ 2 • meanTensor δ τ F b q p := by
  ext i
  simp only [phaseZeroTensor, ← gradientAmplitude_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [finiteMode_mean_identity h hτ δ b q _ _ hp]
  simp only [meanTensor, normalizedMeanError]
  field_simp

end ClosedSurfaceR4.RealModes

end

end OAI
