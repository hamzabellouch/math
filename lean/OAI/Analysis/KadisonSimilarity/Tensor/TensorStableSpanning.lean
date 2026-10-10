import OAI.Analysis.KadisonSimilarity.Tensor.TensorCommutantExtension
import OAI.Analysis.KadisonSimilarity.Tensor.TensorCoefficientMatrix

namespace OAI

/-! Schur--Weyl spanning in the stable range needed after taking a cofinal
tail of the matrix tower. The proof uses a single column with distinct labels. -/

noncomputable section
namespace KadisonSimilarity

open Finset

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

omit [DecidableEq ι] [Fintype α] in
theorem exists_permutation_of_tensor_weights
    (j : ι → α) (hj : Function.Injective j) (f : ι → α)
    (h : ∀ a, tensorLabelCount f a = tensorLabelCount j a) :
    ∃ π : Equiv.Perm ι, f = tensorCoordinatePermutation π j := by
  have he (i : ι) : ∃ k, j k = f i := by
    have hp : 0 < tensorLabelCount f (f i) :=
      Fintype.card_pos_iff.mpr ⟨⟨i, rfl⟩⟩
    rw [h] at hp
    obtain ⟨⟨k, hk⟩⟩ := Fintype.card_pos_iff.mp hp
    exact ⟨k, hk⟩
  choose p hp using he
  have hs : Function.Surjective p := by
    intro k
    have hpos : 0 < tensorLabelCount j (j k) :=
      Fintype.card_pos_iff.mpr ⟨⟨k, rfl⟩⟩
    rw [← h] at hpos
    obtain ⟨⟨i, hi⟩⟩ := Fintype.card_pos_iff.mp hpos
    exact ⟨i, hj ((hp i).trans hi)⟩
  let π := Equiv.ofBijective p (Finite.surjective_iff_bijective.mp hs)
  exact ⟨π, funext fun i => (hp i).symm⟩

private def tensorColumnTransfer (j f : ι → α) : Matrix α α ℂ :=
  ∑ i, Matrix.single (f i) (j i) 1

omit [Fintype α] in
private theorem tensorColumnTransfer_apply
    (j : ι → α) (hj : Function.Injective j) (f : ι → α) (a : α) (i : ι) :
    tensorColumnTransfer j f a (j i) = if a = f i then 1 else 0 := by
  simp [tensorColumnTransfer, Matrix.sum_apply, Matrix.single_apply,
    and_comm, hj.eq_iff, ite_and, eq_comm]

omit [Fintype α] in
private theorem tensorColumnTransfer_column
    (j : ι → α) (hj : Function.Injective j) (f g : ι → α) :
    tupleTensorMatrix (fun _ : ι => tensorColumnTransfer j f) g j =
      if g = f then 1 else 0 := by
  simp only [tupleTensorMatrix_apply, tensorColumnTransfer_apply j hj,
    Fintype.prod_boole]
  congr 1
  exact propext funext_iff.symm

/-- A matrix commuting with every tensor power is determined by its column
at any elementary tensor whose labels are distinct. -/
theorem tensor_commutant_eq_zero_of_column
    (j : ι → α) (hj : Function.Injective j)
    (C : Matrix (ι → α) (ι → α) ℂ)
    (hC : ∀ a : Matrix α α ℂ,
      C * tupleTensorMatrix (fun _ : ι => a) =
        tupleTensorMatrix (fun _ : ι => a) * C)
    (hcolumn : ∀ f, C f j = 0) : C = 0 := by
  ext f g
  have h := congrArg (fun A : Matrix (ι → α) (ι → α) ℂ => A f j)
    (hC (tensorColumnTransfer j g))
  simp only [Matrix.mul_apply] at h
  simp only [tensorColumnTransfer_column j hj] at h
  simpa [hcolumn] using h

/-- The full tensor commutant is spanned by coordinate permutations once a
tuple of distinct labels is available. -/
theorem tensor_commutant_spanned_by_permutations
    (j : ι → α) (hj : Function.Injective j)
    (C : Matrix (ι → α) (ι → α) ℂ)
    (hC : ∀ u : Matrix.unitaryGroup α ℂ,
      C * tupleTensorMatrix (fun _ : ι => (u : Matrix α α ℂ)) =
        tupleTensorMatrix (fun _ : ι => (u : Matrix α α ℂ)) * C) :
    ∃ c : Equiv.Perm ι → ℂ, C = ∑ π, c π • tensorPermutationMatrix (α := α) π := by
  let c : Equiv.Perm ι → ℂ := fun π => C (tensorCoordinatePermutation π j) j
  let S : Matrix (ι → α) (ι → α) ℂ := ∑ π, c π • tensorPermutationMatrix π
  have hinj : Function.Injective (fun π : Equiv.Perm ι => tensorCoordinatePermutation π j) := by
    intro π ρ h
    apply Equiv.ext
    intro i
    exact hj (congrFun h i)
  have hcolumn (f : ι → α) : C f j = S f j := by
    dsimp only [S]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      tensorPermutationMatrix, Matrix.of_apply]
    change C f j = ∑ π, c π * (if f = tensorCoordinatePermutation π j then 1 else 0)
    by_cases hf : ∃ π : Equiv.Perm ι, f = tensorCoordinatePermutation π j
    · obtain ⟨π, rfl⟩ := hf
      rw [Finset.sum_eq_single π]
      · simp [c]
      · intro ρ _ hρ
        have : tensorCoordinatePermutation π j ≠ tensorCoordinatePermutation ρ j :=
          fun h => hρ (hinj h).symm
        simp [this]
      · simp
    · have hz : C f j = 0 := by
        by_contra hc
        apply hf
        apply exists_permutation_of_tensor_weights j hj f
        intro a
        by_contra ha
        exact hc (tensor_commutant_entry_zero_of_weight_ne C hC f j a ha)
      rw [hz]
      symm
      apply Finset.sum_eq_zero
      intro π _
      have hne : f ≠ tensorCoordinatePermutation π j := fun h => hf ⟨π, h⟩
      simp only [hne, ite_false, mul_zero]
  have hS (a : Matrix α α ℂ) :
      S * tupleTensorMatrix (fun _ : ι => a) =
        tupleTensorMatrix (fun _ : ι => a) * S := by
    dsimp [S]
    simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
      constant_tensorMatrix_commutes_permutation]
  have hz : C - S = 0 := tensor_commutant_eq_zero_of_column j hj (C - S)
    (fun a => by
      rw [Matrix.sub_mul, Matrix.mul_sub, tensor_commutant_commutes_matrix C hC a, hS a])
    (fun f => by simp [Matrix.sub_apply, hcolumn f])
  exact ⟨c, sub_eq_zero.mp hz⟩

/-- The stable-range specialization of the published Schur--Weyl input. -/
theorem schurWeylMultilinearSpanning_of_labels [Nonempty α]
    (j : ι → α) (hj : Function.Injective j) : SchurWeylMultilinearSpanning ι α := by
  intro F hF
  obtain ⟨c, hc⟩ := tensor_commutant_spanned_by_permutations j hj
    (tensorCoefficientMatrix F) (tensorCoefficientMatrix_commutes_unitary F hF)
  refine ⟨fun π => c π * (Fintype.card α : ℂ) ^ permutationCycleCount π, ?_⟩
  intro v
  rw [multilinear_eq_trace_tensorCoefficient, hc, Matrix.sum_mul, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro π _
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_comm,
    ← permutationContraction_eq_trace]
  have hn : (Fintype.card α : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [normalizedPermutationContraction]
  have hp : (Fintype.card α : ℂ) ^ permutationCycleCount π *
      ((Fintype.card α : ℂ)⁻¹) ^ permutationCycleCount π = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hn, one_pow]
  calc
    _ = c π * ((Fintype.card α : ℂ) ^ permutationCycleCount π *
        ((Fintype.card α : ℂ)⁻¹) ^ permutationCycleCount π) *
        permutationContraction π v := by rw [hp, mul_one]
    _ = _ := by ring

end KadisonSimilarity

end

end OAI
