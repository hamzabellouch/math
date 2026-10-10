import Mathlib
import OAI.GroupTheory.SimpleAmenable.RandomFields.MatrixDensityCalculus

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section MatrixInverseCalculus
open Classical Matrix Filter
open scoped Topology Matrix.Norms.Elementwise

theorem matrix_differentiableAt_det {ι : Type*} [Fintype ι]
    {A : ℝ → Matrix ι ι ℝ} {t : ℝ} (hA : DifferentiableAt ℝ A t) :
    DifferentiableAt ℝ (fun s => (A s).det) t := by
  convert! (determinantMultilinear.hasFDerivAt (A t)).differentiableAt.comp t hA using 1

theorem matrix_differentiableAt_inverse {ι : Type*} [Fintype ι]
    {A : ℝ → Matrix ι ι ℝ} {t : ℝ} (hA : DifferentiableAt ℝ A t)
    (hunit : IsUnit (A t).det) : DifferentiableAt ℝ (fun s => (A s)⁻¹) t := by
  apply differentiableAt_pi.mpr
  intro i
  apply differentiableAt_pi.mpr
  intro j
  have hAj : DifferentiableAt ℝ (fun s => (A s).adjugate i j) t := by
    simp only [Matrix.adjugate_apply]
    apply matrix_differentiableAt_det
    apply differentiableAt_pi.mpr
    intro k
    apply differentiableAt_pi.mpr
    intro l
    by_cases hk : k=j
    · subst k
      simpa only [Matrix.updateRow_self] using differentiableAt_const ((Pi.single i (1 : ℝ) : ι → ℝ) l)
    · simpa only [Matrix.updateRow_ne hk] using
        (differentiableAt_pi.mp (differentiableAt_pi.mp hA k) l)
  have hd := (matrix_differentiableAt_det hA).inv hunit.ne_zero
  convert! hd.mul hAj using 1
  ext s
  simp only [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.smul_apply,smul_eq_mul,Pi.mul_apply,Pi.inv_apply]

theorem matrix_hasDerivAt_mul {ι : Type*} [Fintype ι]
    {A B : ℝ → Matrix ι ι ℝ} {A' B' : Matrix ι ι ℝ} {t : ℝ}
    (hA : HasDerivAt A A' t) (hB : HasDerivAt B B' t) :
    HasDerivAt (fun s => A s*B s) (A'*B t+A t*B') t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have h (k : ι) := ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hA i)) k).mul
    ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hB k)) j)
  convert! HasDerivAt.fun_sum (fun k (_ : k∈Finset.univ) => h k) using 1
  simp only [Matrix.add_apply,Matrix.mul_apply,Finset.sum_add_distrib]

theorem matrix_hasDerivAt_inverse {ι : Type*} [Fintype ι]
    {A : ℝ → Matrix ι ι ℝ} {A' : Matrix ι ι ℝ} {t : ℝ}
    (hA : HasDerivAt A A' t) (hunit : IsUnit (A t).det) :
    HasDerivAt (fun s => (A s)⁻¹) (-(A t)⁻¹*A'*(A t)⁻¹) t := by
  have hd : HasDerivAt (fun s => (A s)⁻¹) (deriv (fun s => (A s)⁻¹) t) t := by
    apply DifferentiableAt.hasDerivAt
    convert! matrix_differentiableAt_inverse hA.differentiableAt hunit using 1
  let D := deriv (fun s => (A s)⁻¹) t
  have he : ∀ᶠs in 𝓝 t,A s*(A s)⁻¹=1 := by
    have hn := (matrix_differentiableAt_det hA.differentiableAt).continuousAt.eventually_ne hunit.ne_zero
    filter_upwards [hn] with s hs
    exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hs)
  have hp := matrix_hasDerivAt_mul hA hd
  have hz : A'*(A t)⁻¹+A t*D=0 := by
    exact (hp.congr_of_eventuallyEq (Filter.EventuallyEq.symm he)).unique (hasDerivAt_const t (1 : Matrix ι ι ℝ))
  have hm := congrArg (fun M : Matrix ι ι ℝ => (A t)⁻¹*M) hz
  have heq : D=-(A t)⁻¹*A'*(A t)⁻¹ := by
    simp only [Matrix.mul_add,← Matrix.mul_assoc,Matrix.nonsing_inv_mul _ hunit,
      one_mul,mul_zero] at hm
    rw [neg_mul,neg_mul]
    exact eq_neg_of_add_eq_zero_right hm
  rw [← heq]
  exact hd

theorem matrix_hasDerivAt_mulVec {ι : Type*} [Fintype ι]
    {A : ℝ → Matrix ι ι ℝ} {x : ℝ → ι → ℝ}
    {A' : Matrix ι ι ℝ} {x' : ι → ℝ} {t : ℝ}
    (hA : HasDerivAt A A' t) (hx : HasDerivAt x x' t) :
    HasDerivAt (fun s => A s*ᵥx s) (A'*ᵥx t+A t*ᵥx') t := by
  apply hasDerivAt_pi.mpr
  intro i
  have h (j : ι) := ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hA i)) j).mul
    ((hasDerivAt_pi.mp hx) j)
  convert! HasDerivAt.fun_sum (fun j (_ : j∈Finset.univ) => h j) using 1
  simp only [Pi.add_apply,Matrix.mulVec,dotProduct,Finset.sum_add_distrib]

end MatrixInverseCalculus

section AffineVolume
open Classical Matrix MeasureTheory
open scoped ENNReal

noncomputable def matrixAffineEquiv {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (a : ι → ℝ) (hA : IsUnit A.det) :
    (ι → ℝ) ≃ᵐ (ι → ℝ) :=
  ((Matrix.toLinearEquiv (Pi.basisFun ℝ ι) A hA).toContinuousLinearEquiv.toHomeomorph.trans
    (Homeomorph.addLeft a)).toMeasurableEquiv

theorem matrixAffineEquiv_apply {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (a x : ι → ℝ) (hA : IsUnit A.det) :
    matrixAffineEquiv A a hA x=a+A*ᵥx := by
  change a+Matrix.toLin (Pi.basisFun ℝ ι) (Pi.basisFun ℝ ι) A x=_
  rw [Matrix.toLin_eq_toLin',Matrix.toLin'_apply]

theorem matrixAffineEquiv_symm_apply {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (a y : ι → ℝ) (hA : IsUnit A.det) :
    (matrixAffineEquiv A a hA).symm y=A⁻¹*ᵥ(y-a) := by
  apply (matrixAffineEquiv A a hA).injective
  rw [MeasurableEquiv.apply_symm_apply,matrixAffineEquiv_apply,
    Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ hA,Matrix.one_mulVec]
  abel

theorem map_matrix_affine_volume {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (a : ι → ℝ) (hA : IsUnit A.det) :
    Measure.map (fun x => a+A*ᵥx) (volume : Measure (ι → ℝ))=
      ENNReal.ofReal |A.det⁻¹| • volume := by
  change Measure.map ((fun y => a+y) ∘ (Matrix.toLin' A)) volume=_
  rw [← Measure.map_map (by fun_prop) (by fun_prop),
    Real.map_matrix_volume_pi_eq_smul_volume_pi hA.ne_zero,
    Measure.map_smul _ (by fun_prop),map_add_left_eq_self]

theorem integral_matrix_affine {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (a : ι → ℝ) (hA : IsUnit A.det) (f : (ι → ℝ) → ℝ) :
    (∫x,f (a+A*ᵥx))=|A.det⁻¹| *(∫y,f y) := by
  have h := integral_map_equiv (μ := (volume : Measure (ι → ℝ)))
    (matrixAffineEquiv A a hA) f
  rw [show (matrixAffineEquiv A a hA : (ι → ℝ) → (ι → ℝ))=
    (fun x => a+A*ᵥx) from funext (fun x => matrixAffineEquiv_apply A a x hA),map_matrix_affine_volume A a hA,
    integral_smul_measure,ENNReal.toReal_ofReal (abs_nonneg _),smul_eq_mul] at h
  exact h.symm

theorem integral_matrix_affine_inverse {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (a : ι → ℝ) (hA : IsUnit A.det) (f : (ι → ℝ) → ℝ) :
    (∫y,f (A⁻¹*ᵥ(y-a)))=|A.det| *(∫x,f x) := by
  have h := integral_matrix_affine A⁻¹ (-(A⁻¹*ᵥa))
    (isUnit_iff_ne_zero.mpr (by rw [Matrix.det_nonsing_inv,Ring.inverse_eq_inv]; exact inv_ne_zero hA.ne_zero)) f
  convert! h using 1
  · congr 1
    ext y
    rw [Matrix.mulVec_sub]
    simp only [sub_eq_add_neg,add_comm]
  · rw [Matrix.det_nonsing_inv,Ring.inverse_eq_inv,inv_inv]

end AffineVolume

end SimpleAmenable
end
end

end OAI
