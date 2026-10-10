import Mathlib
import OAI.Analysis.AffineBernstein.DeterminantVariation
import OAI.Analysis.AffineBernstein.ParametricAffineArea

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section ParametricChangeOfCoordinates
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/- At a critical point the Hessian chain rule has no second derivative of the
coordinate change. Here it is proved for the actual Fréchet derivatives. -/
lemma second_comp_of_critical {f : F → ℝ} {φ : E → F} {x : E}
    (hf : ContDiffAt ℝ ∞ f (φ x)) (hφ : ContDiffAt ℝ ∞ φ x)
    (hz : fderiv ℝ f (φ x) = 0) (v w : E) :
    fderiv ℝ (fderiv ℝ (f ∘ φ)) x v w =
      fderiv ℝ (fderiv ℝ f) (φ x) (fderiv ℝ φ x v) (fderiv ℝ φ x w) := by
  have hdf := hf.differentiableAt (by simp)
  have hdφ := hφ.differentiableAt (by simp)
  have hff := (hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hφφ := (hφ.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have he : fderiv ℝ (f ∘ φ) =ᶠ[nhds x]
      fun y => (fderiv ℝ f (φ y)).comp (fderiv ℝ φ y) := by
    have hf1 := (hf.of_le (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)).eventually (by simp)
    have hp1 := (hφ.of_le (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)).eventually (by simp)
    filter_upwards [hdφ.continuousAt.eventually hf1, hp1] with y hy hpy
    exact fderiv_comp y (hy.differentiableAt (by norm_num)) (hpy.differentiableAt (by norm_num))
  have hh := (hff.hasFDerivAt.comp x hdφ.hasFDerivAt).clm_comp hφφ.hasFDerivAt
  rw [he.fderiv_eq]
  convert! congrArg (fun A : E →L[ℝ] E →L[ℝ] ℝ => A v w) hh.fderiv using 1
  simp [hz]

end ParametricChangeOfCoordinates

def parametricJacobian {n : ℕ} (φ : Space n → Space n) (x : Space n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => fderiv ℝ φ x (coordinateVector n j) i

lemma hessian_comp_of_critical {n : ℕ} {f : Space n → ℝ} {φ : Space n → Space n}
    {x : Space n} (hf : ContDiffAt ℝ ∞ f (φ x)) (hφ : ContDiffAt ℝ ∞ φ x)
    (hz : fderiv ℝ f (φ x) = 0) :
    hessian (f ∘ φ) x = (parametricJacobian φ x).transpose * hessian f (φ x) * parametricJacobian φ x := by
  ext i j
  change dirDeriv (coordinateVector n i) (dirDeriv (coordinateVector n j) (f ∘ φ)) x = _
  rw [dirDeriv_eq_second (hf.comp x hφ), second_comp_of_critical hf hφ hz,
    ← sum_coordinateVector (fderiv ℝ φ x (coordinateVector n i)),
    ← sum_coordinateVector (fderiv ℝ φ x (coordinateVector n j))]
  simp only [map_sum, map_smul, sum_apply, smul_apply,
    smul_eq_mul, parametricJacobian, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  have hd : fderiv ℝ (fderiv ℝ f) (φ x) (coordinateVector n l) (coordinateVector n k) =
      hessian f (φ x) l k := (dirDeriv_eq_second hf _ _).symm
  rw [hd]
  ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma parametricSecondForm_comp {n : ℕ} {X : Space n → E} {φ : Space n → Space n}
    {x : Space n} (hX : ContDiffAt ℝ ∞ X (φ x)) (hφ : ContDiffAt ℝ ∞ φ x)
    (ν : E →L[ℝ] ℝ) (hν : ν.comp (fderiv ℝ X (φ x)) = 0) :
    parametricSecondForm (X ∘ φ) ν x =
      (parametricJacobian φ x).transpose * parametricSecondForm X ν (φ x) * parametricJacobian φ x := by
  apply hessian_comp_of_critical (ν.contDiff.contDiffAt.comp (φ x) hX) hφ
  have hh := ν.hasFDerivAt.comp (φ x) (hX.differentiableAt (by simp)).hasFDerivAt
  convert! hh.fderiv.trans hν using 1

lemma parametricFrame_comp_matrix {n : ℕ} (b : Module.Basis (Fin n ⊕ Unit) ℝ E)
    {X : Space n → E} {φ : Space n → Space n} {x : Space n}
    (hX : DifferentiableAt ℝ X (φ x)) (hφ : DifferentiableAt ℝ φ x) (ξ : E) :
    b.toMatrix (parametricFrame (X ∘ φ) ξ x) =
      b.toMatrix (parametricFrame X ξ (φ x)) *
        Matrix.fromBlocks (parametricJacobian φ x) 0 0 (1 : Matrix Unit Unit ℝ) := by
  ext i j
  rcases j with j | j
  · simp only [Module.Basis.toMatrix_apply, parametricFrame, Sum.elim_inl]
    rw [fderiv_comp x hX hφ]
    change b.repr (fderiv ℝ X (φ x) (fderiv ℝ φ x (coordinateVector n j))) i = _
    rw [← sum_coordinateVector (fderiv ℝ φ x (coordinateVector n j))]
    simp only [map_sum, map_smul]
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks, parametricJacobian,
      Module.Basis.toMatrix_apply, mul_comm]
  · simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks,
      Module.Basis.toMatrix_apply, parametricFrame]

lemma parametricFrame_comp_det {n : ℕ} (b : Module.Basis (Fin n ⊕ Unit) ℝ E)
    {X : Space n → E} {φ : Space n → Space n} {x : Space n}
    (hX : DifferentiableAt ℝ X (φ x)) (hφ : DifferentiableAt ℝ φ x) (ξ : E) :
    b.det (parametricFrame (X ∘ φ) ξ x) =
      b.det (parametricFrame X ξ (φ x)) * (parametricJacobian φ x).det := by
  simp only [Module.Basis.det_apply, parametricFrame_comp_matrix b hX hφ ξ,
    Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one]

end AffineBernstein
end

end OAI
