import OAI.Analysis.KLS.Stein.SteinHessianDefs
import OAI.Analysis.KLS.Sobolev.TestFunctions
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Topology.Compactness.Compact

namespace OAI

noncomputable section
open Set Matrix MeasureTheory InnerProductSpace
open scoped BigOperators ContDiff Topology Matrix.Norms.Elementwise

namespace LeanBlast.KLS

theorem bl_contDiff_gradient {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (gradient f) := by
  exact (toDual ℝ (Space n)).symm.contDiff.comp (hf.fderiv_right (by simp))

theorem bl_contDiff_hessianMatrix {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (hessianMatrix f) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  exact (((hf.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)).clm_apply
    contDiff_const).clm_apply contDiff_const

section MatrixSmooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  {A : E → Matrix ι ι ℝ}

theorem contDiff_matrix_det (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (fun x => (A x).det) := by
  simp only [Matrix.det_apply']
  fun_prop

theorem contDiff_matrix_adjugate (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (fun x => (A x).adjugate) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  simp only [Matrix.adjugate_apply]
  apply contDiff_matrix_det
  apply contDiff_pi.mpr
  intro a
  apply contDiff_pi.mpr
  intro b
  by_cases h : a = j
  · subst a
    simp only [Matrix.updateRow_self]
    exact contDiff_const
  · simp only [Matrix.updateRow_ne h]
    exact (contDiff_pi.mp (contDiff_pi.mp hA a)) b

theorem contDiff_matrix_inv (hA : ContDiff ℝ ∞ A) (hdet : ∀ x, (A x).det ≠ 0) :
    ContDiff ℝ ∞ (fun x => (A x)⁻¹) := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv]
  exact ((contDiff_matrix_det hA).inv hdet).smul (contDiff_matrix_adjugate hA)

end MatrixSmooth

theorem steinGamma_self_eq_dotProduct {n : ℕ} (V h : Space n → ℝ) (x : Space n) :
    steinGamma V h h x =
      (fun i => gradient h x i) ⬝ᵥ ((hessianMatrix V x)⁻¹ *ᵥ fun i => gradient h x i) := by
  simp [steinGamma, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem steinGamma_self_nonneg {n : ℕ} {V h : Space n → ℝ} {x : Space n}
    (hV : (hessianMatrix V x).PosDef) : 0 ≤ steinGamma V h h x := by
  rw [steinGamma_self_eq_dotProduct]
  simpa only [star_trivial] using hV.inv.posSemidef.dotProduct_mulVec_nonneg
    (fun i => gradient h x i)

theorem contDiff_steinGamma_self {n : ℕ} {V h : Space n → ℝ}
    (hV : ContDiff ℝ ∞ V) (hh : ContDiff ℝ ∞ h)
    (hpos : ∀ x, (hessianMatrix V x).PosDef) :
    ContDiff ℝ ∞ (steinGamma V h h) := by
  have hi : ContDiff ℝ ∞ (fun x => (hessianMatrix V x)⁻¹) :=
    contDiff_matrix_inv (bl_contDiff_hessianMatrix hV) fun x => (hpos x).det_pos.ne'
  have hg := bl_contDiff_gradient hh
  unfold steinGamma
  fun_prop

theorem hasCompactSupport_steinGamma_self {n : ℕ} (V : Space n → ℝ)
    {h : Space n → ℝ} (hh : IsTestFunction h) : HasCompactSupport (steinGamma V h h) := by
  apply HasCompactSupport.intro hh.hasCompactSupport_gradient.isCompact
  intro x hx
  have hzero : gradient h x = 0 := image_eq_zero_of_notMem_tsupport hx
  simp only [steinGamma, hzero, PiLp.zero_apply, zero_mul, Finset.sum_const_zero]

theorem sum_standardBasisVector {n : ℕ} (v : Space n) :
    (∑ i, v i • standardBasisVector i) = v := by
  simpa only [standardBasisVector, EuclideanSpace.basisFun_repr] using
    (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v

theorem second_fderiv_eq_hessianMatrix {n : ℕ} (V : Space n → ℝ) (x u v : Space n) :
    fderiv ℝ (fderiv ℝ V) x u v =
      (fun i => u i) ⬝ᵥ (hessianMatrix V x *ᵥ fun i => v i) := by
  calc
    _ = fderiv ℝ (fderiv ℝ V) x (∑ i, u i • standardBasisVector i)
      (∑ j, v j • standardBasisVector j) := by rw [sum_standardBasisVector, sum_standardBasisVector]
    _ = _ := by
      simp [map_sum, hessianMatrix, Matrix.mulVec, dotProduct, Finset.mul_sum,
        mul_comm, mul_left_comm]
      exact Finset.sum_comm

theorem fderiv_eq_gradient_dotProduct {n : ℕ} {h : Space n → ℝ} {x : Space n}
    (hh : DifferentiableAt ℝ h x) (v : Space n) :
    fderiv ℝ h x v = (fun i => gradient h x i) ⬝ᵥ (fun i => v i) := by
  rw [hh.hasGradientAt.fderiv_apply, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial, dotProduct_comm]

theorem quadratic_schur_positive {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℝ} (hH : H.PosDef) (g v : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (s : ℝ) (hsv : s ≠ 0 ∨ v ≠ 0) :
    0 < v ⬝ᵥ H *ᵥ v + 2 * s * (g ⬝ᵥ v) +
      (g ⬝ᵥ H⁻¹ *ᵥ g + δ) * s ^ 2 := by
  have hmul : H *ᵥ (H⁻¹ *ᵥ g) = g := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hH.det_pos.ne'),
      Matrix.one_mulVec]
  have hsym : Hᵀ = H := hH.isHermitian.eq
  have hcross : (H⁻¹ *ᵥ g) ⬝ᵥ H *ᵥ v = g ⬝ᵥ v := by
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym, hmul]
  have heq : v ⬝ᵥ H *ᵥ v + 2 * s * (g ⬝ᵥ v) +
      (g ⬝ᵥ H⁻¹ *ᵥ g + δ) * s ^ 2 =
      (v + s • (H⁻¹ *ᵥ g)) ⬝ᵥ H *ᵥ (v + s • (H⁻¹ *ᵥ g)) + δ * s ^ 2 := by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, hmul]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, hcross]
    rw [dotProduct_comm v g, dotProduct_comm (H⁻¹ *ᵥ g) g]
    ring
  rw [heq]
  by_cases hs : s = 0
  · rcases hsv with hsv | hv
    · exact (hsv hs).elim
    · simpa [hs] using hH.dotProduct_mulVec_pos hv
  · have hnonneg := hH.posSemidef.dotProduct_mulVec_nonneg (v + s • (H⁻¹ *ᵥ g))
    have hpos : 0 < δ * s ^ 2 := mul_pos hδ (sq_pos_of_ne_zero hs)
    simpa only [star_trivial] using add_pos_of_nonneg_of_pos hnonneg hpos

end LeanBlast.KLS

end

end OAI
