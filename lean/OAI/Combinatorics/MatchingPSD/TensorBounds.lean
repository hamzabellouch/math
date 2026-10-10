import OAI.Combinatorics.MatchingPSD.TransitionMatrices

namespace OAI

universe u_1 u_2 u_3

namespace MatchingSmoothing
open Matrix

variable {C : Type u_1} [Fintype C] [DecidableEq C]

lemma abs_eigenvalue_le_one_stochastic (W : Matrix C C ℝ)
    (hn : ∀ i j, 0 ≤ W i j) (hs : ∀ i, ∑ j, W i j = 1)
    (c : ℝ) (hc : Module.End.HasEigenvalue (Matrix.toLin' W) c) : |c| ≤ 1 := by
  obtain ⟨i, hi⟩ := eigenvalue_mem_ball hc
  rw [mem_closedBall_iff_norm] at hi
  simp only [Real.norm_eq_abs, abs_of_nonneg (hn _ _)] at hi
  have he := Finset.sum_erase_add (Finset.univ : Finset C) (fun j => W i j)
    (Finset.mem_univ i)
  rw [hs] at he
  calc
    |c| = |(c - W i i) + W i i| := by congr 1; ring
    _ ≤ |c - W i i| + |W i i| := abs_add_le _ _
    _ ≤ 1 := by rw [abs_of_nonneg (hn _ _)]; linarith

lemma abs_eigenvalue_le_one_positive_fixed (A : Matrix C C ℝ)
    (hn : ∀ i j, 0 ≤ A i j) (v : C → ℝ) (hv : ∀ i, 0 < v i)
    (hf : A *ᵥ v = v) (c : ℝ)
    (hc : Module.End.HasEigenvalue (Matrix.toLin' A) c) : |c| ≤ 1 := by
  let W : Matrix C C ℝ := fun i j => A i j * v j / v i
  apply abs_eigenvalue_le_one_stochastic W
  · intro i j; exact div_nonneg (mul_nonneg (hn i j) (hv j).le) (hv i).le
  · intro i
    change ∑ j, A i j * v j / v i = 1
    rw [← Finset.sum_div]
    change (A *ᵥ v) i / v i = 1
    rw [hf, div_self (ne_of_gt (hv i))]
  · obtain ⟨x, hx, hnx⟩ := hc.exists_hasEigenvector
    let y : C → ℝ := fun i => x i / v i
    have hy : y ≠ 0 := by
      intro h
      apply hnx
      ext i
      have he := congrFun h i
      change x i / v i = 0 at he
      exact (div_eq_zero_iff.mp he).resolve_right (ne_of_gt (hv i))
    apply Module.End.hasEigenvalue_of_hasEigenvector
    refine ⟨?_, hy⟩
    rw [Module.End.mem_eigenspace_iff]
    ext i
    change ∑ j, (A i j * v j / v i) * (x j / v j) = c * (x i / v i)
    have hh (j : C) : A i j * v j / v i * (x j / v j) = A i j * x j / v i := by
      field_simp [ne_of_gt (hv j), ne_of_gt (hv i)]
    simp_rw [hh]
    rw [← Finset.sum_div]
    have hhx := congrFun (Module.End.mem_eigenspace_iff.mp hx) i
    change ∑ j, A i j * x j = c * x i at hhx
    rw [hhx]
    ring

lemma exists_orthogonal_diagonalization_bounded (A : Matrix C C ℝ)
    (hA : A.IsHermitian) (hn : ∀ i j, 0 ≤ A i j)
    (v : C → ℝ) (hv : ∀ i, 0 < v i) (hf : A *ᵥ v = v) :
    ∃ U : Matrix C C ℝ, ∃ d : C → ℝ,
      U.transpose * U = 1 ∧ (∀ i, |d i| ≤ 1) ∧ A = U * diagonal d * U.transpose := by
  refine ⟨hA.eigenvectorUnitary, hA.eigenvalues, ?_, ?_, ?_⟩
  · simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hA.eigenvectorUnitary.property.1
  · intro i
    apply abs_eigenvalue_le_one_positive_fixed A hn v hv hf
    apply Module.End.hasEigenvalue_of_hasEigenvector
    refine ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]
      exact hA.mulVec_eigenvectorBasis i
    · intro h
      have he : hA.eigenvectorBasis i = 0 := by
        exact PiLp.ext (fun j => congrFun h j)
      exact (hA.eigenvectorBasis.orthonormal.ne_zero i) he
  · simpa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hA.spectral_theorem

end MatchingSmoothing

namespace MatchingSmoothing
open Matrix
variable {H : Type u_2} {C : Type u_3} [Fintype H] [Fintype C] [DecidableEq H] [DecidableEq C]

noncomputable def commonColoringsProdEquiv (σ : Equiv.Perm (H × Bool)) :
    ({f : H × Bool → C // pairConstant f ∧ pairConstant (f ∘ σ)} ×
      {f : H × Bool → C // pairConstant f ∧ pairConstant (f ∘ σ)}) ≃
    {f : H × Bool → C × C // pairConstant f ∧ pairConstant (f ∘ σ)} where
  toFun fg := ⟨fun v => (fg.1.1 v, fg.2.1 v),
    ⟨fun i => Prod.ext (fg.1.2.1 i) (fg.2.2.1 i),
      fun i => Prod.ext (fg.1.2.2 i) (fg.2.2.2 i)⟩⟩
  invFun f := (⟨fun v => (f.1 v).1, ⟨fun i => congrArg Prod.fst (f.2.1 i),
      fun i => congrArg Prod.fst (f.2.2 i)⟩⟩,
    ⟨fun v => (f.1 v).2, ⟨fun i => congrArg Prod.snd (f.2.1 i),
      fun i => congrArg Prod.snd (f.2.2 i)⟩⟩)
  left_inv _ := rfl
  right_inv _ := rfl

lemma commonColorings_square (σ : Equiv.Perm (H × Bool)) :
    (Fintype.card {f : H × Bool → C // pairConstant f ∧ pairConstant (f ∘ σ)}) ^ 2 =
    Fintype.card {f : H × Bool → C × C // pairConstant f ∧ pairConstant (f ∘ σ)} := by
  rw [pow_two, ← Fintype.card_prod]
  exact Fintype.card_congr (commonColoringsProdEquiv σ)

omit [Fintype C] [DecidableEq H] [DecidableEq C] in
lemma pairWeight_nonneg (A : Matrix C C ℝ) (hn : ∀ i j, 0 ≤ A i j)
    (f : H × Bool → C) : 0 ≤ pairWeight A f := by
  exact Finset.prod_nonneg (fun _ _ => hn _ _)

lemma pairWeight_overlap_square_moment (A : Matrix C C ℝ)
    (hA : A.IsHermitian) (hn : ∀ i j, 0 ≤ A i j)
    (v : C → ℝ) (hv : ∀ i, 0 < v i) (hf : A *ᵥ v = v) :
    (∑ σ : Equiv.Perm (H × Bool),
      (∑ f : H × Bool → C, pairWeight A f * pairWeight A (f ∘ σ)) ^ 2) ≤
    (Fintype.card (Equiv.Perm (H × Bool)) : ℝ) *
      (Fintype.card H + 1 : ℝ) ^ (Fintype.card C) ^ 2 := by
  obtain ⟨U, d, hU, hd, he⟩ := exists_orthogonal_diagonalization_bounded A hA hn v hv hf
  have hp (σ : Equiv.Perm (H × Bool)) :
      (∑ f : H × Bool → C, pairWeight A f * pairWeight A (f ∘ σ)) ^ 2 ≤
      (Fintype.card {f : H × Bool → C × C // pairConstant f ∧ pairConstant (f ∘ σ)} : ℝ) := by
    rw [← commonColorings_square, Nat.cast_pow]
    apply pow_le_pow_left₀
    · exact Finset.sum_nonneg (fun f _ => mul_nonneg (pairWeight_nonneg A hn f)
        (pairWeight_nonneg A hn (f ∘ σ)))
    · rw [he]
      exact pairWeight_overlap_le U d hU hd σ
  have h := (Finset.sum_le_sum (fun σ (_ : σ ∈ Finset.univ) => hp σ)).trans
    (common_pairColorings_moment (H := H) (β := C × C))
  simpa only [Fintype.card_prod, pow_two] using h

noncomputable def normalizedPairMatrix (γ : Matrix C C ℝ) (π : C → ℝ) : Matrix C C ℝ :=
  fun i j => γ i j / (Real.sqrt (π i) * Real.sqrt (π j))

omit [Fintype C] [DecidableEq C] in
lemma normalizedPairMatrix_nonneg (γ : Matrix C C ℝ) (π : C → ℝ)
    (hn : ∀ i j, 0 ≤ γ i j) : ∀ i j, 0 ≤ normalizedPairMatrix γ π i j := by
  intro i j
  exact div_nonneg (hn i j) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

omit [Fintype C] [DecidableEq C] in
lemma normalizedPairMatrix_hermitian (γ : Matrix C C ℝ) (π : C → ℝ)
    (hs : γ.IsHermitian) : (normalizedPairMatrix γ π).IsHermitian := by
  rw [Matrix.IsHermitian.ext_iff] at hs ⊢
  intro i j
  simp only [star_trivial] at hs ⊢
  simp only [normalizedPairMatrix, hs j i, mul_comm]

omit [DecidableEq C] in
lemma normalizedPairMatrix_fixed (γ : Matrix C C ℝ) (π : C → ℝ)
    (hp : ∀ i, 0 < π i) (hs : ∀ i, ∑ j, γ i j = π i) :
    normalizedPairMatrix γ π *ᵥ (fun i => Real.sqrt (π i)) = fun i => Real.sqrt (π i) := by
  ext i
  have he (j : C) : γ i j / (Real.sqrt (π i) * Real.sqrt (π j)) * Real.sqrt (π j) =
      γ i j / Real.sqrt (π i) := by
    field_simp [ne_of_gt (Real.sqrt_pos.mpr (hp j)), ne_of_gt (Real.sqrt_pos.mpr (hp i))]
  change ∑ j, γ i j / (Real.sqrt (π i) * Real.sqrt (π j)) * Real.sqrt (π j) = _
  simp_rw [he]
  rw [← Finset.sum_div, hs]
  exact (div_eq_iff (ne_of_gt (Real.sqrt_pos.mpr (hp i)))).mpr
    (Real.mul_self_sqrt (hp i).le).symm

end MatchingSmoothing

end OAI
