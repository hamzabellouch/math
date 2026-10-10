import OAI.Probability.SignedSweeps.PolarDecomposition

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

lemma cayley_real_denom_ne (x : ℝ) : (x : ℂ) - Complex.I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this

lemma cayley_real_norm (x : ℝ) : ‖((x : ℂ) + Complex.I) / ((x : ℂ) - Complex.I)‖ = 1 := by
  rw [norm_div]
  have hn : ‖(x : ℂ) + Complex.I‖ = ‖(x : ℂ) - Complex.I‖ := by
    calc
      _ = ‖star ((x : ℂ) + Complex.I)‖ := (norm_star _).symm
      _ = _ := by simp [sub_eq_add_neg]
  rw [hn, div_self (norm_ne_zero_iff.mpr (cayley_real_denom_ne x))]

lemma cayley_real_injective :
    Function.Injective (fun x : ℝ => ((x : ℂ) + Complex.I) / ((x : ℂ) - Complex.I)) := by
  intro x y h
  have hh := (div_eq_div_iff (cayley_real_denom_ne x) (cayley_real_denom_ne y)).mp h
  have hi := congrArg Complex.im hh
  simp only [Complex.mul_im, Complex.add_re, Complex.ofReal_re, Complex.I_re, add_zero,
    Complex.sub_re, sub_zero, Complex.add_im, Complex.ofReal_im, Complex.I_im,
    zero_add, Complex.sub_im, zero_sub, mul_neg, mul_one, one_mul] at hi
  linarith

lemma infinite_complex_unit_sphere : {z : ℂ | ‖z‖ = 1}.Infinite := by
  apply (Set.infinite_range_of_injective cayley_real_injective).mono
  rintro _ ⟨x, rfl⟩
  exact cayley_real_norm x

lemma span_unit_monomial_evaluations {I S : Type*} [Fintype I]
    (v : I → S →₀ ℕ) (hv : Function.Injective v) :
    Submodule.span ℂ (Set.range (fun x : {z : S → ℂ // ∀ i, ‖z i‖ = 1} =>
      fun i => (v i).prod (fun s k => x.1 s ^ k))) = ⊤ := by
  by_contra h
  obtain ⟨f, hf, hker⟩ := Submodule.exists_le_ker_of_lt_top _
    (lt_top_iff_ne_top.mpr h)
  let b := Pi.basisFun ℂ I
  let P : MvPolynomial S ℂ := ∑ i, MvPolynomial.monomial (v i) (f (b i))
  have hP : P = 0 := by
    apply MvPolynomial.funext_set (fun _ => {z : ℂ | ‖z‖ = 1})
      (fun _ => infinite_complex_unit_sphere)
    intro x hx
    simp only [map_zero, P, map_sum, MvPolynomial.eval_monomial]
    have hx' : ∀ i, ‖x i‖ = 1 := fun i => hx i (Set.mem_univ i)
    have hh := hker (Submodule.subset_span
      (Set.mem_range_self (⟨x, hx'⟩ : {z : S → ℂ // ∀ i, ‖z i‖ = 1})))
    change f (fun i => (v i).prod (fun s k => x s ^ k)) = 0 at hh
    rw [← b.sum_repr (fun i => (v i).prod (fun s k => x s ^ k))] at hh
    simpa only [map_sum, map_smul, b, Pi.basisFun_repr, smul_eq_mul, mul_comm] using hh
  have hz (i : I) : f (b i) = 0 := by
    have hc := congrArg (fun polynomial : MvPolynomial S ℂ => polynomial.coeff (v i)) hP
    simpa [P, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, hv.eq_iff] using hc
  apply hf
  apply b.ext
  exact fun i => hz i

def wordTensorMatrixHom (p : ℕ) (C : Type*) [Fintype C] :
    Matrix C C ℂ →* Matrix (Fin p → C) (Fin p → C) ℂ where
  toFun := wordTensorMatrix p
  map_one' := wordTensorMatrix_one
  map_mul' := wordTensorMatrix_mul

def unitaryTensorAlgebra (p : ℕ) (C : Type*) [Fintype C] :
    Subalgebra ℂ (Matrix (Fin p → C) (Fin p → C) ℂ) :=
  Algebra.adjoin ℂ (Set.range (fun U : Matrix.unitaryGroup C ℂ => wordTensorMatrix p U.1))

lemma unitaryTensorAlgebra_toSubmodule {p : ℕ} {C : Type*} [Fintype C] :
    (unitaryTensorAlgebra p C).toSubmodule = Submodule.span ℂ
      (Set.range (fun U : Matrix.unitaryGroup C ℂ => wordTensorMatrix p U.1)) := by
  let f := (wordTensorMatrixHom p C).comp (Matrix.unitaryGroup C ℂ).subtype
  have hs : (Set.range (fun U : Matrix.unitaryGroup C ℂ => wordTensorMatrix p U.1)) =
      (MonoidHom.mrange f : Set (Matrix (Fin p → C) (Fin p → C) ℂ)) := rfl
  unfold unitaryTensorAlgebra
  rw [Algebra.adjoin_eq_span, hs, (MonoidHom.mrange f).closure_eq]

lemma wordUnitary_mem {p : ℕ} {C : Type*} [Fintype C] (U : Matrix.unitaryGroup C ℂ) :
    wordTensorMatrix p U.1 ∈ unitaryTensorAlgebra p C :=
  Algebra.subset_adjoin (Set.mem_range_self U)

lemma diagonal_unitary {C : Type*} [Fintype C] (x : C → ℂ) (hx : ∀ c, ‖x c‖ = 1) :
    Matrix.diagonal x ∈ Matrix.unitaryGroup C ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  change Matrix.diagonal x * (Matrix.diagonal x).conjTranspose = 1
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    simp [RCLike.mul_conj, hx]
  · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]

theorem diagonal_wordTensor_mem {p : ℕ} {C : Type*} [Fintype C] (x : C → ℂ) :
    wordTensorMatrix p (Matrix.diagonal x) ∈ unitaryTensorAlgebra p C := by
  let I : Type _ := {v : C →₀ ℕ // ∃ w : Fin p → C, v = wordHistogram w}
  have : Finite I := by
    apply Finite.of_surjective (fun w : Fin p → C =>
      (⟨wordHistogram w, ⟨w, rfl⟩⟩ : I))
    rintro ⟨v, w, rfl⟩
    exact ⟨w, rfl⟩
  let : Fintype I := Fintype.ofFinite I
  let L : (I → ℂ) →ₗ[ℂ] Matrix (Fin p → C) (Fin p → C) ℂ :=
    { toFun := fun f => Matrix.diagonal (fun w => f ⟨wordHistogram w, ⟨w, rfl⟩⟩)
      map_add' := by
        intro f g; ext w y; by_cases h : w = y <;> simp [h]
      map_smul' := by
        intro r f; ext w y; by_cases h : w = y <;> simp [h] }
  have hL (z : C → ℂ) :
      L (fun i : I => i.1.prod (fun c k => z c ^ k)) = wordTensorMatrix p (Matrix.diagonal z) := by
    ext w y
    by_cases h : w = y
    · subst y
      change (Matrix.diagonal _) w w = _
      simp only [Matrix.diagonal_apply_eq, wordTensorMatrix]
      exact wordHistogram_monomial_eval w z
    · change (Matrix.diagonal _) w y = _
      rw [Matrix.diagonal_apply_ne _ h]
      obtain ⟨i, hi⟩ := Function.ne_iff.mp h
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (Matrix.diagonal_apply_ne _ hi)
  have hspan := span_unit_monomial_evaluations (fun i : I => i.1) Subtype.val_injective
  have hle : Submodule.span ℂ (Set.range (fun z : {z : C → ℂ // ∀ c, ‖z c‖ = 1} =>
      fun i : I => i.1.prod (fun c k => z.1 c ^ k))) ≤ (unitaryTensorAlgebra p C).toSubmodule.comap L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨z, rfl⟩
    change L _ ∈ unitaryTensorAlgebra p C
    rw [hL]
    exact wordUnitary_mem ⟨Matrix.diagonal z.1, diagonal_unitary z.1 z.2⟩
  rw [hspan] at hle
  have ht := hle (Submodule.mem_top : (fun i : I => i.1.prod (fun c k => x c ^ k)) ∈ ⊤)
  change L _ ∈ unitaryTensorAlgebra p C at ht
  rwa [hL] at ht

lemma hermitian_wordTensor_mem {p : ℕ} {C : Type*} [Fintype C]
    (A : Matrix C C ℂ) (hA : A.IsHermitian) :
    wordTensorMatrix p A ∈ unitaryTensorAlgebra p C := by
  rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rw [wordTensorMatrix_mul, wordTensorMatrix_mul]
  apply Subalgebra.mul_mem
  · exact Subalgebra.mul_mem _ (wordUnitary_mem hA.eigenvectorUnitary)
      (diagonal_wordTensor_mem _)
  · exact wordUnitary_mem (star hA.eigenvectorUnitary)

theorem wordTensor_mem_unitary {p : ℕ} {C : Type*} [Fintype C]
    (A : Matrix C C ℂ) : wordTensorMatrix p A ∈ unitaryTensorAlgebra p C := by
  let φ := LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun C ℂ)
  obtain ⟨U, P, hP, he⟩ := exists_unitary_positive_factor (φ.symm A)
  have hU : φ U.toLinearEquiv.toLinearMap ∈ Matrix.unitaryGroup C ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, ← map_star, ← map_mul]
    have hcan : U.toLinearEquiv.toLinearMap * star U.toLinearEquiv.toLinearMap = 1 := by
      rw [LinearMap.star_eq_adjoint, LinearIsometryEquiv.adjoint_toLinearMap_eq_symm]
      apply LinearMap.ext
      intro x
      exact U.apply_symm_apply x
    rw [hcan, map_one]
  have hp : (φ P).IsHermitian := by
    change star (φ P) = φ P
    rw [← map_star, LinearMap.star_eq_adjoint, hP.isSymmetric.adjoint_eq]
  have hA : A = φ U.toLinearEquiv.toLinearMap * φ P := by
    rw [← map_mul, ← he, φ.apply_symm_apply]
  rw [hA, wordTensorMatrix_mul]
  exact Subalgebra.mul_mem _ (wordUnitary_mem ⟨_, hU⟩) (hermitian_wordTensor_mem _ hp)

theorem span_unitary_wordTensor {p : ℕ} {C : Type*} [Fintype C] :
    Submodule.span ℂ
      (Set.range (fun U : Matrix.unitaryGroup C ℂ => wordTensorMatrix p U.1)) =
        wordCommutant p C := by
  apply le_antisymm
  · rw [← span_wordTensorMatrix]
    exact Submodule.span_mono (by rintro _ ⟨U, rfl⟩; exact ⟨U.1, rfl⟩)
  · rw [← span_wordTensorMatrix, ← unitaryTensorAlgebra_toSubmodule]
    apply Submodule.span_le.mpr
    rintro _ ⟨A, rfl⟩
    exact wordTensor_mem_unitary A

end SignedSweeps
end

end OAI
