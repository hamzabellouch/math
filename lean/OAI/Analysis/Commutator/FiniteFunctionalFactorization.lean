import Mathlib
import OAI.Analysis.Commutator.CoefficientForm2

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.OperatorFunctionals

open InnerProductSpace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def coefficientDual (φ : StrongDual ℂ (H →L[ℂ] H)) (b : H) : StrongDual ℂ H :=
  φ.comp ((rankOne ℂ : H →L[ℂ] H →L⋆[ℂ] H →L[ℂ] H).flip b)

@[simp] lemma coefficientDual_apply (φ : StrongDual ℂ (H →L[ℂ] H)) (a b : H) :
    coefficientDual φ b a=φ (rankOne ℂ a b) := rfl

def coefficient (φ : StrongDual ℂ (H →L[ℂ] H)) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun b => (toDual ℂ H).symm (coefficientDual φ b)
      map_add' := by
        intro b c
        apply ext_inner_right ℂ
        intro a
        simp only [inner_add_left,toDual_symm_apply,coefficientDual_apply,
          map_add]
      map_smul' := by
        intro z b
        apply ext_inner_right ℂ
        intro a
        simp only [inner_smul_left,toDual_symm_apply,coefficientDual_apply,
          map_smulₛₗ,RingHom.id_apply,smul_eq_mul] }
    ‖φ‖ (by
      intro b
      change ‖(toDual ℂ H).symm (coefficientDual φ b)‖≤_
      rw [LinearIsometryEquiv.norm_map]
      apply opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      intro a
      change ‖φ (rankOne ℂ a b)‖≤_
      exact (φ.le_opNorm (rankOne ℂ a b)).trans_eq (by simp [mul_comm,mul_left_comm,mul_assoc]))

@[simp] lemma inner_coefficient (φ : StrongDual ℂ (H →L[ℂ] H)) (a b : H) :
    inner ℂ (coefficient φ b) a=φ (rankOne ℂ a b) := by
  change inner ℂ ((toDual ℂ H).symm (coefficientDual φ b)) a=_
  rw [toDual_symm_apply,coefficientDual_apply]

variable {ι : Type*} [Fintype ι]

lemma eq_sum_coefficients (φ : StrongDual ℂ (H →L[ℂ] H))
    (b : OrthonormalBasis ι ℂ H) (T : H →L[ℂ] H) :
    φ T=∑ i, inner ℂ (coefficient φ (b i)) (T (b i)) := by
  simp only [inner_coefficient,←map_sum]
  congr 1
  ext x
  simp only [sum_apply,rankOne_apply]
  simpa only [map_sum,map_smul,OrthonormalBasis.repr_apply_apply] using congrArg T (b.sum_repr x).symm

omit [CompleteSpace H] in
lemma norm_sq_sum_of_orthogonal (v : ι → H)
    (hv : Pairwise (fun i j => inner ℂ (v i) (v j)=0)) :
    ‖∑ i, v i‖^2=∑ i, ‖v i‖^2 := by
  classical
  simp only [@norm_sq_eq_re_inner ℂ H, sum_inner,inner_sum,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  refine Finset.sum_eq_single i ?_ ?_
  · intro j _ hji
    simp [hv hji]
  · simp

omit [CompleteSpace H] [Fintype ι] in
lemma inner_normalized_of_ne (v : ι → H)
    (hv : Pairwise (fun i j => inner ℂ (v i) (v j)=0)) :
    Pairwise (fun i j => inner ℂ ((‖v i‖⁻¹ : ℝ) • v i)
      ((‖v j‖⁻¹ : ℝ) • v j)=0) := by
  intro i j hij
  simp [hv hij]

omit [CompleteSpace H] in
lemma orthogonalColumn_norm_le (b : OrthonormalBasis ι ℂ H) (u : ι → H)
    (hu : Pairwise (fun i j => inner ℂ (u i) (u j)=0))
    (hn : ∀ i, ‖u i‖≤1) : ‖∑ i, rankOne ℂ (u i) (b i)‖≤1 := by
  apply opNorm_le_bound _ zero_le_one
  intro x
  simp only [one_mul,sum_apply,rankOne_apply]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_sum_of_orthogonal _ (by
    intro i j hij
    simp [hu hij])]
  calc
    _ ≤ ∑ i, ‖inner ℂ (b i) x‖^2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul,mul_pow]
      exact mul_le_of_le_one_right (sq_nonneg _) (by nlinarith [norm_nonneg (u i),hn i])
    _ ≤ ‖x‖^2 := b.orthonormal.sum_inner_products_le x

omit [CompleteSpace H] in
lemma orthogonalColumn_apply_basis (b : OrthonormalBasis ι ℂ H) (u : ι → H) (j : ι) :
    (∑ i, rankOne ℂ (u i) (b i)) (b j)=u j := by
  classical
  simp [sum_apply,rankOne_apply,b.inner_eq_ite]

variable [FiniteDimensional ℂ H]

def singularBasis (R : H →L[ℂ] H) :
    OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H :=
  (R.toLinearMap.isSymmetric_adjoint_comp_self).eigenvectorBasis rfl

lemma singularBasis_orthogonal (R : H →L[ℂ] H) :
    Pairwise (fun i j => inner ℂ (R (singularBasis R i)) (R (singularBasis R j))=0) := by
  intro i j hij
  rw [←ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ ((R.toLinearMap.adjoint ∘ₗ R.toLinearMap) (singularBasis R i))
    (singularBasis R j)=0
  have he : (R.toLinearMap.adjoint ∘ₗ R.toLinearMap) (singularBasis R i)=
      (R.toLinearMap.isSymmetric_adjoint_comp_self.eigenvalues rfl i : ℂ) • singularBasis R i :=
    R.toLinearMap.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis rfl i
  rw [he]
  simp [(singularBasis R).inner_eq_zero hij]

omit [CompleteSpace H] [FiniteDimensional ℂ H] in
lemma norm_inv_smul_norm_le_one (v : H) : ‖(‖v‖⁻¹ : ℝ) • v‖≤1 := by
  by_cases hv : v=0
  · simp [hv]
  · have hn : ‖v‖≠0 := norm_ne_zero_iff.mpr hv
    simp [norm_smul,hn]

omit [CompleteSpace H] [FiniteDimensional ℂ H] in
lemma inner_norm_inv_smul (v : H) :
    inner ℂ v ((‖v‖⁻¹ : ℝ) • v)=(‖v‖ : ℂ) := by
  by_cases hv : v=0
  · simp [hv]
  · have hn : ‖v‖≠0 := norm_ne_zero_iff.mpr hv
    rw [inner_smul_right_eq_smul,inner_self_eq_norm_sq_to_K,Complex.real_smul]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hn]
    rfl

lemma sum_singular_coefficients_le (φ : StrongDual ℂ (H →L[ℂ] H)) :
    ∑ i, ‖coefficient φ (singularBasis (coefficient φ) i)‖≤‖φ‖ := by
  let b := singularBasis (coefficient φ)
  let v := fun i => coefficient φ (b i)
  let u := fun i => (‖v i‖⁻¹ : ℝ) • v i
  let P := ∑ i, rankOne ℂ (u i) (b i)
  have hP : ‖P‖≤1 := orthogonalColumn_norm_le b u
    (inner_normalized_of_ne v (singularBasis_orthogonal (coefficient φ)))
    (fun i => norm_inv_smul_norm_le_one (v i))
  have hφP : φ P=(∑ i, ‖v i‖ : ℝ) := by
    rw [eq_sum_coefficients φ b P,Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i _
    change inner ℂ (v i) (P (b i))=_
    change inner ℂ (v i) ((∑ j, rankOne ℂ (u j) (b j)) (b i))=_
    rw [orthogonalColumn_apply_basis]
    exact inner_norm_inv_smul (v i)
  have hh := (φ.le_opNorm P).trans (mul_le_of_le_one_right (norm_nonneg φ) hP)
  rw [hφP,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))] at hh
  exact hh

omit [CompleteSpace H] [FiniteDimensional ℂ H] in
lemma balanced_inner (v b : H) (T : H →L[ℂ] H) :
    inner ℂ ((Real.sqrt ‖v‖)⁻¹ • v) (T (Real.sqrt ‖v‖ • b))=inner ℂ v (T b) := by
  by_cases hv : v=0
  · simp [hv]
  have hs : Real.sqrt ‖v‖≠0 := Real.sqrt_ne_zero'.mpr (norm_pos_iff.mpr hv)
  rw [map_smul_of_tower,inner_smul_left_eq_smul,inner_smul_right_eq_smul,
    smul_smul,inv_mul_cancel₀ hs,one_smul]

omit [CompleteSpace H] [FiniteDimensional ℂ H] in
lemma balanced_right_norm_sq (v : H) : ‖(Real.sqrt ‖v‖)⁻¹ • v‖^2=‖v‖ := by
  by_cases hv : v=0
  · simp [hv]
  have hs : Real.sqrt ‖v‖≠0 := Real.sqrt_ne_zero'.mpr (norm_pos_iff.mpr hv)
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)),mul_pow,inv_pow]
  rw [Real.sq_sqrt (norm_nonneg v)]
  field_simp [norm_ne_zero_iff.mpr hv]

omit [CompleteSpace H] [FiniteDimensional ℂ H] in
lemma balanced_left_norm_sq (v b : H) (hb : ‖b‖=1) :
    ‖Real.sqrt ‖v‖ • b‖^2=‖v‖ := by
  simp [norm_smul,hb,Real.sq_sqrt (norm_nonneg v)]

theorem exists_finite_factorization (φ : StrongDual ℂ (H →L[ℂ] H)) :
    ∃ x y : PiLp 2 (fun _ : Fin (Module.finrank ℂ H) => H),
      (∀ T : H →L[ℂ] H, φ T=∑ i, inner ℂ (y i) (T (x i))) ∧ ‖x‖*‖y‖≤‖φ‖ := by
  let b := singularBasis (coefficient φ)
  let v := fun i => coefficient φ (b i)
  let x : PiLp 2 (fun _ : Fin (Module.finrank ℂ H) => H) :=
    WithLp.toLp 2 (fun i => Real.sqrt ‖v i‖ • b i)
  let y : PiLp 2 (fun _ : Fin (Module.finrank ℂ H) => H) :=
    WithLp.toLp 2 (fun i => (Real.sqrt ‖v i‖)⁻¹ • v i)
  refine ⟨x,y,?_,?_⟩
  · intro T
    rw [eq_sum_coefficients φ b T]
    apply Finset.sum_congr rfl
    intro i _
    exact (balanced_inner (v i) (b i) T).symm
  · have hx : ‖x‖^2=∑ i, ‖v i‖ := by
      rw [PiLp.norm_sq_eq_of_L2]
      apply Finset.sum_congr rfl
      intro i _
      exact balanced_left_norm_sq (v i) (b i) (b.orthonormal.1 i)
    have hy : ‖y‖^2=∑ i, ‖v i‖ := by
      rw [PiLp.norm_sq_eq_of_L2]
      apply Finset.sum_congr rfl
      intro i _
      exact balanced_right_norm_sq (v i)
    have hxy : ‖x‖=‖y‖ := (sq_eq_sq₀ (norm_nonneg x) (norm_nonneg y)).mp (hx.trans hy.symm)
    rw [←hxy,←pow_two,hx]
    exact sum_singular_coefficients_le φ

end Kadison.OperatorFunctionals

end

end
end

end OAI
