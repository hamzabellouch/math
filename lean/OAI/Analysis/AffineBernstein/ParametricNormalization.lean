import Mathlib
import OAI.Analysis.AffineBernstein.MatrixConcavity
import OAI.Analysis.AffineBernstein.ParametricAffineArea

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma parametricFrame_smul_det {n : ℕ} (b : Module.Basis (Fin n ⊕ Unit) ℝ E)
    (X : Space n → E) (ξ : E) (x : Space n) (c : ℝ) :
    b.det (parametricFrame X (c • ξ) x) = c * b.det (parametricFrame X ξ x) := by
  have he (r : ℝ) : parametricFrame X (r • ξ) x =
      Function.update (parametricFrame X ξ x) (Sum.inr ()) (r • ξ) := by
    funext i
    rcases i with i | i
    · simp [parametricFrame]
    · cases i; simp [parametricFrame]
  rw [he, b.det.map_update_smul]
  have hh : Function.update (parametricFrame X ξ x) (Sum.inr ()) ξ =
      parametricFrame X ξ x := by
    apply Function.update_eq_self
  rw [hh, smul_eq_mul]

lemma parametricSecondForm_smul {n : ℕ} {U : Set (Space n)} (hU : IsOpen U)
    {X : Space n → E} (hX : ContDiffOn ℝ ∞ X U) (ν : E →L[ℝ] ℝ)
    (c : ℝ) {x : Space n} (hx : x ∈ U) :
    parametricSecondForm X (c • ν) x = c • parametricSecondForm X ν x := by
  unfold parametricSecondForm
  change hessian (fun y => c * ν (X y)) x = _
  exact hessian_const_mul hU (ν.contDiff.comp_contDiffOn hX) c hx

/- Invariance under positive rescaling of the conormal and reciprocal scaling
of the transverse vector. Both are actual multilinear expressions. -/
theorem parametricAreaDensity_normalize {n : ℕ}
    (b : Module.Basis (Fin n ⊕ Unit) ℝ E) {U : Set (Space n)} (hU : IsOpen U)
    {X : Space n → E} (hX : ContDiffOn ℝ ∞ X U) (ν : E →L[ℝ] ℝ) (ξ : E)
    {c : ℝ} (hc : 0 < c) {x : Space n} (hx : x ∈ U)
    (hH : 0 ≤ (parametricSecondForm X ν x).det) :
    parametricAreaDensity b X (c • ν) (c⁻¹ • ξ) x =
      parametricAreaDensity b X ν ξ x := by
  rw [parametricAreaDensity, parametricSecondForm_smul hU hX ν c hx,
    Matrix.det_smul, Fintype.card_fin, parametricFrame_smul_det, abs_mul,
    abs_of_pos (inv_pos.mpr hc)]
  simp only [Real.rpow_eq_pow]
  rw [Real.mul_rpow (pow_nonneg hc.le _) hH,
    Real.mul_rpow (inv_nonneg.mpr hc.le) (abs_nonneg _),
    ← Real.rpow_natCast_mul hc.le n, Real.inv_rpow hc.le]
  have he : (n : ℝ) * (1 / ((n : ℝ) + 2)) = (n : ℝ) / ((n : ℝ) + 2) := by ring
  rw [he]
  have hz : c ^ ((n : ℝ) / ((n : ℝ) + 2)) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hc _)
  unfold parametricAreaDensity
  simp only [Real.rpow_eq_pow]
  field_simp

/- A tangent vector can be added to the transverse column without changing
its affine volume. -/
lemma parametricFrame_add_tangent_det {n : ℕ}
    (b : Module.Basis (Fin n ⊕ Unit) ℝ E) (X : Space n → E)
    (ξ : E) (x v : Space n) :
    b.det (parametricFrame X (ξ + fderiv ℝ X x v) x) =
      b.det (parametricFrame X ξ x) := by
  let A := b.toMatrix (parametricFrame X ξ x)
  let coeff : Fin n ⊕ Unit → ℝ := Sum.elim v (fun _ => 1)
  have he : b.toMatrix (parametricFrame X (ξ + fderiv ℝ X x v) x) =
      A.updateCol (Sum.inr ()) (fun k => ∑ i, coeff i • A k i) := by
    ext i j
    rcases j with j | j
    · simp [A, Matrix.updateCol, Module.Basis.toMatrix_apply, parametricFrame]
    · cases j
      simp only [Module.Basis.toMatrix_apply, parametricFrame, Sum.elim_inr,
        Matrix.updateCol_self]
      rw [← sum_coordinateVector v]
      simp [A, coeff, Fintype.sum_sum_type, map_sum, map_smul, Module.Basis.toMatrix_apply,
        parametricFrame, add_comm]
  rw [Module.Basis.det_apply, he, Matrix.det_updateCol_sum]
  simp [coeff, A, Module.Basis.det_apply]

lemma parametricAreaDensity_add_tangent {n : ℕ}
    (b : Module.Basis (Fin n ⊕ Unit) ℝ E) (X : Space n → E)
    (ν : E →L[ℝ] ℝ) (ξ : E) (x v : Space n) :
    parametricAreaDensity b X ν (ξ + fderiv ℝ X x v) x =
      parametricAreaDensity b X ν ξ x := by
  simp only [parametricAreaDensity, parametricFrame_add_tangent_det]

end AffineBernstein
end

end OAI
