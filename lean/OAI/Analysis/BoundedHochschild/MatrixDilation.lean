import Mathlib

namespace OAI

/-! Matrix dilations, tracial matrix algebras and bounded linear maps. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
namespace HochschildMatrixDilation
noncomputable section
open scoped Matrix ComplexOrder
open Complex
variable {A : Type*} [CStarAlgebra A]

abbrev Mat (A : Type*) := CStarMatrix (Fin 2) (Fin 2) A

def diag (a b : A) : Mat A := CStarMatrix.ofMatrix !![a,0;0,b]

def offdiag (a b : A) : Mat A := CStarMatrix.ofMatrix !![0,a;b,0]

@[simp] lemma diag_zero_zero : diag (0:A) 0 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl
@[simp] lemma diag_one_one : diag (1:A) 1 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl
@[simp] lemma diag_add (a b c d : A) : diag (a+c) (b+d) = diag a b + diag c d := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [diag]
@[simp] lemma diag_smul (z : ℂ) (a b : A) : diag (z • a) (z • b) = z • diag a b := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [diag]
@[simp] lemma diag_mul (a b c d : A) : diag a b * diag c d = diag (a*c) (b*d) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [diag, CStarMatrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma star_diag (a b : A) : star (diag a b) = diag (star a) (star b) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [diag, CStarMatrix.star_eq_conjTranspose]
@[simp] lemma star_offdiag (a b : A) : star (offdiag a b) = offdiag (star b) (star a) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [offdiag, CStarMatrix.star_eq_conjTranspose]
@[simp] lemma offdiag_mul (a b c d : A) :
    offdiag a b * offdiag c d = diag (a*d) (b*c) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [diag, offdiag, CStarMatrix.mul_apply, Fin.sum_univ_two]

 
def diagHom : A × A →⋆ₐ[ℂ] Mat A where
  toFun a := diag a.1 a.2
  map_one' := diag_one_one
  map_mul' a b := (diag_mul _ _ _ _).symm
  map_zero' := diag_zero_zero
  map_add' a b := diag_add _ _ _ _
  commutes' z := by
    ext i j; fin_cases i <;> fin_cases j <;>
      rfl
  map_star' a := (star_diag _ _).symm

variable [PartialOrder A] [StarOrderedRing A]

lemma norm_diag_le (a b : A) : ‖diag a b‖ ≤ max ‖a‖ ‖b‖ := by
  exact NonUnitalStarAlgHom.norm_apply_le diagHom (a,b)

omit [PartialOrder A] [StarOrderedRing A] in
lemma offdiag_selfAdjoint (a : A) : IsSelfAdjoint (offdiag a (star a)) := by
  change star (offdiag a (star a)) = _
  simp

lemma offdiag_norm_le_one (a : A) (ha : ‖a‖ ≤ 1) : ‖offdiag a (star a)‖ ≤ 1 := by
  have hsq : ‖offdiag a (star a)‖^2 ≤ 1 := by
    rw [← (offdiag_selfAdjoint a).norm_mul_self, offdiag_mul]
    refine (norm_diag_le _ _).trans (max_le ?_ ?_)
    · calc
        ‖a * star a‖ ≤ ‖a‖ * ‖star a‖ := norm_mul_le _ _
        _ ≤ 1 := by rw [norm_star]; nlinarith [norm_nonneg a]
    · calc
        ‖star a * a‖ ≤ ‖star a‖ * ‖a‖ := norm_mul_le _ _
        _ ≤ 1 := by rw [norm_star]; nlinarith [norm_nonneg a]
  exact (sq_le_one_iff₀ (norm_nonneg _)).mp hsq

def flipUnitary : unitary (Mat A) :=
  ⟨offdiag 1 1, by rw [Unitary.mem_iff]; simp⟩

 

def dilation (a : A) (ha : ‖a‖ ≤ 1) : unitary (Mat A) :=
  (selfAdjoint.unitarySelfAddISMul
    ⟨offdiag a (star a), offdiag_selfAdjoint a⟩ (offdiag_norm_le_one a ha)) * flipUnitary

local instance : NonUnitalContinuousFunctionalCalculus ℝ (Mat A) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus

local instance : NonnegSpectrumClass ℝ (Mat A) :=
  CStarAlgebra.instNonnegSpectrumClass

lemma dilation_sub_diag (a : A) (ha : ‖a‖ ≤ 1) :
    (dilation a ha : Mat A) - diag a (star a) =
    Complex.I • (CFC.sqrt (1 - offdiag a (star a) ^ 2) * offdiag 1 1) := by
  change (offdiag a (star a) + Complex.I • CFC.sqrt (1 - offdiag a (star a)^2)) *
    offdiag 1 1 - diag a (star a) = _
  rw [add_mul, smul_mul_assoc, offdiag_mul, mul_one, mul_one]
  abel

lemma diagEntry_nonneg (M : Mat A) (hM : 0 ≤ M) (i : Fin 2) : 0 ≤ M i i := by
  have hs := CFC.sqrt_nonneg M
  have he : M = star (CFC.sqrt M) * CFC.sqrt M := by
    rw [hs.isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self M hM]
  rw [he, CStarMatrix.mul_apply]
  simp only [CStarMatrix.star_apply]
  exact Finset.sum_nonneg fun j _ => star_mul_self_nonneg _

def matrixTraceLinear (τ : A →ₚ[ℂ] ℂ) : Mat A →ₗ[ℂ] ℂ where
  toFun M := (τ (M 0 0) + τ (M 1 1)) / 2
  map_add' M N := by simp only [CStarMatrix.add_apply, map_add]; ring
  map_smul' z M := by
    simp only [CStarMatrix.smul_apply, map_smul, smul_eq_mul, RingHom.id_apply]
    ring

 
def matrixTrace (τ : A →ₚ[ℂ] ℂ) : Mat A →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ (matrixTraceLinear τ) (fun M hM =>
    div_nonneg (add_nonneg (τ.map_nonneg (diagEntry_nonneg M hM 0))
      (τ.map_nonneg (diagEntry_nonneg M hM 1))) (by norm_num))

lemma matrixTrace_apply (τ : A →ₚ[ℂ] ℂ) (M : Mat A) :
    matrixTrace τ M = (τ (M 0 0) + τ (M 1 1)) / 2 := rfl

@[simp] lemma matrixTrace_diag (τ : A →ₚ[ℂ] ℂ) (a b : A) :
    matrixTrace τ (diag a b) = (τ a + τ b)/2 := rfl

lemma matrixTrace_one (τ : A →ₚ[ℂ] ℂ) (hτ : τ 1 = 1) : matrixTrace τ 1 = 1 := by
  rw [← diag_one_one, matrixTrace_diag, hτ]
  ring

lemma matrixTrace_tracial (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ a b : A, τ (a*b) = τ (b*a)) (M N : Mat A) :
    matrixTrace τ (M*N) = matrixTrace τ (N*M) := by
  simp only [matrixTrace_apply, CStarMatrix.mul_apply, Fin.sum_univ_two, map_add]
  rw [htr (M 0 0), htr (M 0 1), htr (M 1 0), htr (M 1 1)]
  ring

lemma matrixTrace_norm_sq (τ : A →ₚ[ℂ] ℂ) (M : Mat A) :
    ‖(matrixTrace τ).toPreGNS M‖^2 =
    (‖τ.toPreGNS (M 0 0)‖^2 + ‖τ.toPreGNS (M 1 0)‖^2 +
      ‖τ.toPreGNS (M 0 1)‖^2 + ‖τ.toPreGNS (M 1 1)‖^2) / 2 := by
  apply Complex.ofReal_injective
  push_cast
  simp only [PositiveLinearMap.preGNS_norm_sq, PositiveLinearMap.ofPreGNS_toPreGNS,
    matrixTrace_apply, CStarMatrix.mul_apply, Fin.sum_univ_two, CStarMatrix.star_apply,
    map_add]
  ring

lemma matrixTrace_faithful (τ : A →ₚ[ℂ] ℂ)
    (hf : ∀ a : A, τ (star a*a) = 0 → a = 0) (M : Mat A)
    (hM : matrixTrace τ (star M*M) = 0) : M = 0 := by
  have hm : ‖(matrixTrace τ).toPreGNS M‖^2 = 0 := by
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_pow, Complex.ofReal_zero,
      PositiveLinearMap.preGNS_norm_sq, PositiveLinearMap.ofPreGNS_toPreGNS] using hM
  rw [matrixTrace_norm_sq] at hm
  have hn (a : A) (h : ‖τ.toPreGNS a‖^2 = 0) : a = 0 := by
    apply hf
    simpa only [Complex.ofReal_pow, Complex.ofReal_zero,
      PositiveLinearMap.preGNS_norm_sq, PositiveLinearMap.ofPreGNS_toPreGNS] using
      congrArg (fun r : ℝ => (r:ℂ)) h
  have h00 := sq_nonneg ‖τ.toPreGNS (M 0 0)‖
  have h10 := sq_nonneg ‖τ.toPreGNS (M 1 0)‖
  have h01 := sq_nonneg ‖τ.toPreGNS (M 0 1)‖
  have h11 := sq_nonneg ‖τ.toPreGNS (M 1 1)‖
  have hz00 : M 0 0 = 0 := hn _ (by linarith)
  have hz10 : M 1 0 = 0 := hn _ (by linarith)
  have hz01 : M 0 1 = 0 := hn _ (by linarith)
  have hz11 : M 1 1 = 0 := hn _ (by linarith)
  ext i j
  fin_cases i <;> fin_cases j
  · exact hz00
  · exact hz01
  · exact hz10
  · exact hz11

open scoped Matrix.Norms.Elementwise in
 
def matrixMap (R : A →L[ℂ] A) : Mat A →L[ℂ] Mat A where
  toLinearMap := CStarMatrix.mapₗ R.toLinearMap
  cont := by
    let e := CStarMatrix.ofMatrixL (m:=Fin 2) (n:=Fin 2) (A:=A)
    have hc : Continuous (fun M : Mat A => fun i j => R (e.symm M i j)) := by
      apply continuous_pi; intro i
      apply continuous_pi; intro j
      exact R.continuous.comp ((continuous_apply j).comp ((continuous_apply i).comp e.symm.continuous))
    exact e.continuous.comp hc

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma matrixMap_apply (R : A →L[ℂ] A) (M : Mat A) (i j : Fin 2) :
    matrixMap R M i j = R (M i j) := rfl

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma matrixMap_diag (R : A →L[ℂ] A) (a b : A) :
    matrixMap R (diag a b) = diag (R a) (R b) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [diag]

lemma dilation_defect_nonneg (a : A) (ha : ‖a‖ ≤ 1) :
    0 ≤ (1 - offdiag a (star a)^2 : Mat A) := by
  have hself := offdiag_selfAdjoint a
  have hnon : 0 ≤ (offdiag a (star a) : Mat A)^2 := by
    simpa only [hself.star_eq, pow_two] using (star_mul_self_nonneg (offdiag a (star a)))
  rw [sub_nonneg, ← CStarAlgebra.norm_le_one_iff_of_nonneg _ hnon,
    pow_two, hself.norm_mul_self]
  exact (sq_le_one_iff₀ (norm_nonneg _)).mpr (offdiag_norm_le_one a ha)

lemma dilation_error_sq (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ a b : A, τ (a*b) = τ (b*a)) (a : A) (ha : ‖a‖ ≤ 1) :
    ‖(matrixTrace τ).toPreGNS ((dilation a ha : Mat A) - diag a (star a))‖^2 =
      (τ (1-star a*a)).re := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_pow, PositiveLinearMap.preGNS_norm_sq]
  simp only [PositiveLinearMap.ofPreGNS_toPreGNS, dilation_sub_diag,
    star_smul, star_mul, smul_mul_smul, Complex.star_def, Complex.conj_I, neg_mul,
    Complex.I_mul_I, neg_neg, one_smul]
  let d : Mat A := CFC.sqrt (1 - offdiag a (star a)^2)
  have hd : star d = d := (CFC.sqrt_nonneg _).isSelfAdjoint.star_eq
  change matrixTrace τ ((star (offdiag 1 1) * star d) * (d * offdiag 1 1)) = _
  rw [mul_assoc, ← mul_assoc (star d), hd, CFC.sqrt_mul_sqrt_self _ (dilation_defect_nonneg a ha)]
  rw [← mul_assoc, matrixTrace_tracial τ htr, ← mul_assoc, star_offdiag,
    star_one, offdiag_mul, one_mul, diag_one_one, one_mul]
  rw [pow_two, offdiag_mul]
  have he : (1 : Mat A) - diag (a*star a) (star a*a) =
      diag (1-a*star a) (1-star a*a) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [diag]
  rw [he, matrixTrace_diag]
  have ht : τ (1-a*star a) = τ (1-star a*a) := by simp only [map_sub, htr a (star a)]
  rw [ht]
  have hnon : 0 ≤ 1-star a*a := by
    rw [sub_nonneg, ← CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg a),
      CStarRing.norm_star_mul_self]
    nlinarith [norm_nonneg a]
  have hre : (τ (1-star a*a)).im = 0 := (Complex.nonneg_iff.mp (τ.map_nonneg hnon)).2.symm

  rw [← Complex.re_add_im (τ (1-star a*a)), hre]
  simp

end
end HochschildMatrixDilation
end

end OAI
