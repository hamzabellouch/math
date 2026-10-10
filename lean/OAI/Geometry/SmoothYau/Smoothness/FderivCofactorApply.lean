import Mathlib
import OAI.Geometry.SmoothYau.Estimates.PiolaCancellation

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def determinantMultilinear : ContinuousMultilinearMap ℝ (fun _ : ι => ι → ℝ) ℝ :=
  { (Matrix.detRowAlternating : (ι → ℝ) [⋀^ι]→ₗ[ℝ] ℝ).toMultilinearMap with
    cont := by
      change Continuous (fun A : Matrix ι ι ℝ => A.det)
      simp only [Matrix.det_apply']
      fun_prop }

lemma determinantMultilinear_apply (A : Matrix ι ι ℝ) : determinantMultilinear A = A.det := rfl

lemma det_updateRow_eq (A : Matrix ι ι ℝ) (hA : IsUnit A.det) (i : ι) (v : ι → ℝ) :
    (A.updateRow i v).det = (v ᵥ* A⁻¹) i * A.det := by
  have hv : v = ∑ k, (v ᵥ* A⁻¹) k • A k := by
    ext j
    have hh := congrFun (Matrix.vecMul_vecMul v A⁻¹ A) j
    rw [Matrix.nonsing_inv_mul _ hA, Matrix.vecMul_one] at hh
    simpa only [Matrix.vecMul, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hh.symm
  conv_lhs => arg 1; arg 3; rw [hv]
  exact Matrix.det_updateRow_sum A i (v ᵥ* A⁻¹)


lemma fderiv_det_apply (A H : Matrix ι ι ℝ) (hA : IsUnit A.det) :
    fderiv ℝ (Matrix.det : Matrix ι ι ℝ → ℝ) A H =
      A.det * Matrix.trace (H * A⁻¹) := by
  have hd := determinantMultilinear.hasFDerivAt A
  have hd' := hd.fderiv
  change fderiv ℝ (determinantMultilinear (ι := ι)) A H = _
  rw [hd']
  change (determinantMultilinear.linearDeriv A) H = _
  erw [ContinuousMultilinearMap.linearDeriv_apply]
  change (∑ i, (A.updateRow i (H i)).det) = _
  simp only [det_updateRow_eq A hA, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.vecMul, dotProduct, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma differentiable_det : Differentiable ℝ (Matrix.det : Matrix ι ι ℝ → ℝ) :=
  fun A => (determinantMultilinear.hasFDerivAt A).differentiableAt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma fderiv_det_comp_apply (A : E → Matrix ι ι ℝ) {x : E}
    (hA : DifferentiableAt ℝ A x) (hx : IsUnit (A x).det) (v : E) :
    fderiv ℝ (fun y => (A y).det) x v =
      (A x).det * Matrix.trace ((fderiv ℝ A x v) * (A x)⁻¹) := by
  change fderiv ℝ (Matrix.det ∘ A) x v = _
  rw [fderiv_comp x (differentiable_det (A x)) hA]
  exact fderiv_det_apply _ _ hx

end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma differentiableAt_matrix_inv {A : E → Matrix ι ι ℝ} {x : E}
    (hA : DifferentiableAt ℝ A x) (hx : IsUnit (A x).det) :
    DifferentiableAt ℝ (fun y => (A y)⁻¹) x := by
  have he (i j : ι) : DifferentiableAt ℝ (fun y => A y i j) x :=
    (differentiableAt_pi.mp (differentiableAt_pi.mp hA i)) j
  have hd : DifferentiableAt ℝ (fun y => (A y).det) x :=
    (differentiable_det _).comp x hA
  apply differentiableAt_pi.mpr
  intro i
  apply differentiableAt_pi.mpr
  intro j
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul,
    Matrix.adjugate_apply]
  apply (hd.inv (isUnit_iff_ne_zero.mp hx)).mul
  simp only [Matrix.det_apply']
  apply DifferentiableAt.fun_sum
  intro σ _
  apply (differentiableAt_const _).mul
  have hp (k : ι) : DifferentiableAt ℝ
      (fun y => (A y).updateRow j (Pi.single i 1) (σ k) k) x := by
    by_cases hk : σ k = j
    · simp only [hk, Matrix.updateRow_self]
      exact differentiableAt_const _
    · simp only [Matrix.updateRow_ne hk]
      exact he _ _
  exact (HasFDerivAt.finsetProd (u := Finset.univ)
    (fun k _ => (hp k).hasFDerivAt)).differentiableAt

omit [DecidableEq ι] in
lemma fderiv_matrix_apply {A : E → Matrix ι ι ℝ} {x : E}
    (hA : DifferentiableAt ℝ A x) (v : E) (i j : ι) :
    fderiv ℝ A x v i j = fderiv ℝ (fun y => A y i j) x v := by
  have hr (i : ι) := differentiableAt_pi.mp hA i
  have hc (i j : ι) := differentiableAt_pi.mp (hr i) j
  change (fderiv ℝ (fun y i => A y i) x v) i j = _
  rw [fderiv_pi hr]
  change (fderiv ℝ (fun y j => A y i j) x v) j = _
  rw [fderiv_pi (hc i)]
  rfl

lemma fderiv_matrix_inv_apply {A : E → Matrix ι ι ℝ} {x : E}
    (hA : DifferentiableAt ℝ A x) (hx : IsUnit (A x).det) (v : E) :
    fderiv ℝ (fun y => (A y)⁻¹) x v =
      -(A x)⁻¹ * (fderiv ℝ A x v) * (A x)⁻¹ := by
  have hB := differentiableAt_matrix_inv hA hx
  have hAn (i j : ι) := (differentiableAt_pi.mp (differentiableAt_pi.mp hA i)) j
  have hBn (i j : ι) := (differentiableAt_pi.mp (differentiableAt_pi.mp hB i)) j
  have hev : ∀ᶠ y in 𝓝 x, IsUnit (A y).det := by
    have hc : ContinuousAt (fun y => (A y).det) x :=
      ((differentiable_det _).comp x hA).continuousAt
    filter_upwards [hc.eventually_ne (isUnit_iff_ne_zero.mp hx)] with y hy
    exact isUnit_iff_ne_zero.mpr hy
  have heq : A x * (fderiv ℝ (fun y => (A y)⁻¹) x v) +
      (fderiv ℝ A x v) * (A x)⁻¹ = 0 := by
    ext i j
    have hloc : (fun y => ∑ k, A y i k * (A y)⁻¹ k j) =ᶠ[𝓝 x]
        (fun _ => (1 : Matrix ι ι ℝ) i j) := by
      filter_upwards [hev] with y hy
      exact congrFun (congrFun (Matrix.mul_nonsing_inv (A y) hy) i) j
    have hD := congrArg (fun D : E →L[ℝ] ℝ => D v) hloc.fderiv_eq
    rw [fderiv_const_apply] at hD
    erw [fderiv_fun_sum (u := Finset.univ) (A := fun k y => A y i k * (A y)⁻¹ k j)
      (fun k _ => (hAn i k).mul (hBn k j))] at hD
    simp only [fderiv_fun_mul (hAn _ _) (hBn _ _), _root_.sum_apply,
      _root_.add_apply, _root_.smul_apply, smul_eq_mul, _root_.zero_apply] at hD
    simpa only [Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply,
      fderiv_matrix_apply hA, fderiv_matrix_apply hB, ← Finset.sum_add_distrib,
      mul_comm] using hD
  have hh := congrArg (fun B : Matrix ι ι ℝ => (A x)⁻¹ * B) heq
  rw [Matrix.mul_add, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hx,
    Matrix.one_mul, Matrix.mul_zero] at hh
  exact eq_neg_of_add_eq_zero_left hh |>.trans (by simp only [Matrix.neg_mul, Matrix.mul_assoc])

end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma fderiv_cofactor_apply {A : E → Matrix ι ι ℝ} {x : E}
    (hA : DifferentiableAt ℝ A x) (hx : IsUnit (A x).det) (v : E) (i k : ι) :
    fderiv ℝ (fun y => (A y).det * (A y)⁻¹ i k) x v =
      (A x).det * (Matrix.trace (fderiv ℝ A x v * (A x)⁻¹) * (A x)⁻¹ i k -
        ((A x)⁻¹ * (fderiv ℝ A x v) * (A x)⁻¹) i k) := by
  have hB := differentiableAt_matrix_inv hA hx
  have hBn := (differentiableAt_pi.mp (differentiableAt_pi.mp hB i)) k
  have hd : DifferentiableAt ℝ (fun y => (A y).det) x :=
    (differentiable_det _).comp x hA
  rw [fderiv_fun_mul hd hBn]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  rw [fderiv_det_comp_apply A hA hx v, ← fderiv_matrix_apply hB,
    fderiv_matrix_inv_apply hA hx v]
  simp only [Matrix.neg_mul, Matrix.neg_apply]
  ring

lemma piola_of_curl {A : E → Matrix ι ι ℝ} {x : E} (b : ι → E)
    (hA : DifferentiableAt ℝ A x) (hx : IsUnit (A x).det)
    (hcurl : ∀ i l m, fderiv ℝ A x (b i) l m = fderiv ℝ A x (b m) l i)
    (k : ι) :
    ∑ i, fderiv ℝ (fun y => (A y).det * (A y)⁻¹ i k) x (b i) = 0 := by
  simp_rw [fderiv_cofactor_apply hA hx]
  rw [← Finset.mul_sum, piola_cancellation _ _ hcurl, mul_zero]


end YauCounterexamples
end

end OAI
