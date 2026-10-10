import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import OAI.Geometry.SurfaceImmersion.Geometry.LowJetChainRule

namespace OAI

/-! Finite moment cancellation for smoothing kernels on the coordinate plane.
Distinct positive dilations give a kernel of mass one whose required low
moments vanish. This is the algebraic step in finite-order smoothing. -/
noncomputable section
open scoped BigOperators Matrix

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory
open JetPolynomial (Base)

/-- The transpose Vandermonde system prescribes all moments through order `r`. -/
theorem exists_dilation_weights (r : ℕ) (b : Fin (r + 1) → ℝ)
    (hb : Function.Injective b) :
    ∃ c : Fin (r + 1) → ℝ, ∀ j : Fin (r + 1),
      ∑ i, c i * b i ^ j.val = if j = 0 then 1 else 0 := by
  let A : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ := (Matrix.vandermonde b).transpose
  have hdet : A.det ≠ 0 := by
    simpa only [A, Matrix.det_transpose] using Matrix.det_vandermonde_ne_zero_iff.mpr hb
  have hunit : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hdet)
  obtain ⟨c, hc⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr hunit) (Pi.single 0 1)
  refine ⟨c, ?_⟩
  intro j
  have h := congrFun hc j
  simpa only [A, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    Matrix.vandermonde_apply, Pi.single_apply, mul_comm] using h

/-- Positive integral dilation factors suffice, so each dilation preserves
compact support and smoothness. -/
theorem exists_positive_dilation_weights (r : ℕ) :
    ∃ c : Fin (r + 1) → ℝ, ∀ j : Fin (r + 1),
      ∑ i, c i * ((i.val + 1 : ℕ) : ℝ) ^ j.val = if j = 0 then 1 else 0 := by
  apply exists_dilation_weights r
  intro i j hij
  apply Fin.ext
  exact Nat.add_right_cancel (Nat.cast_injective hij)

def monomial (α : Fin 2 → ℕ) (x : Base) : ℝ := ∏ i, x i ^ α i

def degree (α : Fin 2 → ℕ) : ℕ := ∑ i, α i

lemma monomial_smul (α : Fin 2 → ℕ) (a : ℝ) (x : Base) :
    monomial α (a • x) = a ^ degree α * monomial α x := by
  simp only [monomial, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    degree, Finset.prod_pow_eq_pow_sum]

/-- The normalized dilation is appropriate to the two-dimensional chart. -/
def dilate (K : Base → ℝ) (a : ℝ) (x : Base) : ℝ := (a ^ 2)⁻¹ * K (a⁻¹ • x)

lemma moment_dilate (K : Base → ℝ) (α : Fin 2 → ℕ) {a : ℝ} (ha : 0 < a) :
    (∫ x, monomial α x * dilate K a x) = a ^ degree α * ∫ x, monomial α x * K x := by
  have hdim : Module.finrank ℝ Base = 2 := by simp [Base]
  have hm (x : Base) : monomial α x = a ^ degree α * monomial α (a⁻¹ • x) := by
    rw [← monomial_smul, smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
  have heq : (fun x => monomial α x * dilate K a x) =
      (fun x => (a ^ degree α / a ^ 2) *
        ((fun y => monomial α y * K y) (a⁻¹ • x))) := by
    funext x
    rw [hm x]
    unfold dilate
    ring
  rw [heq, integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg volume (fun x => monomial α x * K x) ha.le]
  rw [hdim, smul_eq_mul]
  field_simp [ha.ne']

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
