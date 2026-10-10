import OAI.Analysis.HilbertCrouzeix.NumericalRange

namespace OAI

noncomputable section

open Complex Set
open scoped TensorProduct Matrix.Norms.L2Operator Classical ComplexConjugate

namespace HilbertCrouzeix

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section Elementary
omit [CompleteSpace H]

def compression (A : H →L[ℂ] H) (E : Submodule ℂ H) [E.HasOrthogonalProjection] :
    E →L[ℂ] E := E.orthogonalProjectionOnto.comp (A.comp E.subtypeL)

theorem numericalRange_compression_subset (A : H →L[ℂ] H) (E : Submodule ℂ H)
    [E.HasOrthogonalProjection] : numericalRange (compression A E) ⊆ numericalRange A := by
  rintro z ⟨x, hx, rfl⟩
  refine ⟨(x : H), hx, ?_⟩
  exact (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left x (A x)).symm

theorem compression_pow (A : H →L[ℂ] H) (E : Submodule ℂ H)
    [E.HasOrthogonalProjection] (x : E) {d : ℕ}
    (hmem : ∀ k ≤ d, (A ^ k) (x : H) ∈ E) {k : ℕ} (hk : k ≤ d) :
    (((compression A E) ^ k) x : H) = (A ^ k) (x : H) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk' : k ≤ d := by omega
    have hn : A ((A ^ k) (x : H)) ∈ E := by
      simpa only [pow_succ', mul_apply_eq_comp] using hmem (k + 1) hk
    rw [pow_succ', pow_succ', mul_apply_eq_comp, mul_apply_eq_comp]
    change E.starProjection (A (((compression A E) ^ k) x : H)) = _
    rw [ih hk']
    exact Submodule.starProjection_eq_self_iff.mpr hn

def iterateSpace {q : ℕ} (A : H →L[ℂ] H) (d : ℕ) (x : Fin q → H) : Submodule ℂ H :=
  Submodule.span ℂ (Set.range fun t : Fin (d + 1) × Fin q => (A ^ t.1.val) (x t.2))

instance iterateSpace_finiteDimensional {q : ℕ} (A : H →L[ℂ] H) (d : ℕ)
    (x : Fin q → H) : FiniteDimensional ℂ (iterateSpace A d x) :=
  FiniteDimensional.span_of_finite ℂ (Set.finite_range _)

theorem pow_mem_iterateSpace {q : ℕ} (A : H →L[ℂ] H) (d : ℕ) (x : Fin q → H)
    {k : ℕ} (hk : k ≤ d) (j : Fin q) : (A ^ k) (x j) ∈ iterateSpace A d x := by
  apply Submodule.subset_span
  exact ⟨(⟨k, by omega⟩, j), rfl⟩

theorem mem_iterateSpace {q : ℕ} (A : H →L[ℂ] H) (d : ℕ) (x : Fin q → H)
    (j : Fin q) : x j ∈ iterateSpace A d x := by
  simpa using pow_mem_iterateSpace A d x (Nat.zero_le d) j

def completedIsometry {V : Type*} {W : Type*}
    [NormedAddCommGroup V] [NormedAddCommGroup W] [NormedSpace ℂ V] [NormedSpace ℂ W]
    (f : V →ₗᵢ[ℂ] W) : UniformSpace.Completion V →ₗᵢ[ℂ] UniformSpace.Completion W :=
  { f.toContinuousLinearMap.completion.toLinearMap with
    norm_map' := f.isometry.completion_map.norm_map_of_map_zero
      (f.toContinuousLinearMap.completion.map_zero) }

def tensorInclusion (E : Submodule ℂ H) (m : ℕ) :
    Amplification E m →ₗᵢ[ℂ] Amplification H m :=
  completedIsometry (TensorProduct.mapIsometry E.subtypeₗᵢ (.id : CoeffSpace m →ₗᵢ[ℂ] CoeffSpace m))

@[simp] theorem tensorInclusion_tmul (E : Submodule ℂ H) {m : ℕ}
    (x : E) (v : CoeffSpace m) :
    tensorInclusion E m (↑(x ⊗ₜ[ℂ] v)) = (↑((x : H) ⊗ₜ[ℂ] v) : Amplification H m) := by
  change (TensorProduct.mapIsometry E.subtypeₗᵢ (.id : CoeffSpace m →ₗᵢ[ℂ] CoeffSpace m)
    ).toContinuousLinearMap.completion (↑(x ⊗ₜ[ℂ] v)) = _
  rw [ContinuousLinearMap.completion_apply_coe]
  rfl

@[simp] theorem tensorOp_tmul {m : ℕ} (A : H →L[ℂ] H) (B : Coeff m)
    (x : H) (v : CoeffSpace m) :
    tensorOp A B (↑(x ⊗ₜ[ℂ] v)) =
      (↑(A x ⊗ₜ[ℂ] (Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℂ) B) v) : Amplification H m) := by
  simp only [tensorOp, ContinuousLinearMap.completion_apply_coe, TensorProduct.mapL_tmul]

theorem polynomialEval_compression_tmul (A : H →L[ℂ] H) (E : Submodule ℂ H)
    [E.HasOrthogonalProjection] {m d : ℕ} (B : Fin (d + 1) → Coeff m)
    (x : E) (v : CoeffSpace m) (hmem : ∀ k ≤ d, (A ^ k) (x : H) ∈ E) :
    tensorInclusion E m (polynomialEval (compression A E) B (↑(x ⊗ₜ[ℂ] v))) =
      polynomialEval A B (↑((x : H) ⊗ₜ[ℂ] v)) := by
  simp only [polynomialEval, sum_apply, map_sum, tensorOp_tmul,
    tensorInclusion_tmul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [compression_pow A E x hmem (Nat.le_of_lt_succ k.isLt)]

@[simp] theorem completion_coe_sum {V : Type*} [NormedAddCommGroup V]
    {ι : Type*} (s : Finset ι) (f : ι → V) :
    (↑(∑ i ∈ s, f i) : UniformSpace.Completion V) = ∑ i ∈ s, (↑(f i) : UniformSpace.Completion V) :=
  map_sum (UniformSpace.Completion.toCompl : V →+ UniformSpace.Completion V) f s

theorem exists_finite_compression {m d : ℕ} (A : H →L[ℂ] H)
    (B : Fin (d + 1) → Coeff m) (ξ : H ⊗[ℂ] CoeffSpace m) :
    ∃ (E : Submodule ℂ H) (hE : FiniteDimensional ℂ E),
      letI : FiniteDimensional ℂ E := hE
      ∃ η : Amplification E m,
        tensorInclusion E m η = (↑ξ : Amplification H m) ∧
        tensorInclusion E m (polynomialEval (compression A E) B η) =
          polynomialEval A B (↑ξ) := by
  obtain ⟨q, x, v, rfl⟩ := TensorProduct.exists_sum_tmul_eq ξ
  let E := iterateSpace A d x
  let xE (j : Fin q) : E := ⟨x j, mem_iterateSpace A d x j⟩
  let η : Amplification E m := ∑ j : Fin q, (↑(xE j ⊗ₜ[ℂ] v j) : Amplification E m)
  refine ⟨E, inferInstance, η, ?_, ?_⟩
  · simp only [η, map_sum, tensorInclusion_tmul, completion_coe_sum]
    rfl
  · simp only [η, map_sum, completion_coe_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact polynomialEval_compression_tmul A E B (xE j) (v j)
      (fun k hk => pow_mem_iterateSpace A d x hk j)

theorem exists_finite_compression_norm_bound {m d : ℕ} (A : H →L[ℂ] H)
    (B : Fin (d + 1) → Coeff m) (ξ : H ⊗[ℂ] CoeffSpace m) :
    ∃ (E : Submodule ℂ H) (hE : FiniteDimensional ℂ E),
      letI : FiniteDimensional ℂ E := hE
      ‖polynomialEval A B (↑ξ)‖ ≤ ‖polynomialEval (compression A E) B‖ * ‖ξ‖ := by
  obtain ⟨E, hE, η, hη, hp⟩ := exists_finite_compression A B ξ
  let : FiniteDimensional ℂ E := hE
  refine ⟨E, hE, ?_⟩
  calc
    ‖polynomialEval A B (↑ξ)‖ =
        ‖tensorInclusion E m (polynomialEval (compression A E) B η)‖ := congrArg norm hp.symm
    _ = ‖polynomialEval (compression A E) B η‖ := (tensorInclusion E m).norm_map _
    _ ≤ ‖polynomialEval (compression A E) B‖ * ‖η‖ :=
      (polynomialEval (compression A E) B).le_opNorm η
    _ = ‖polynomialEval (compression A E) B‖ * ‖ξ‖ := by
      rw [← (tensorInclusion E m).norm_map η, hη, UniformSpace.Completion.norm_coe]

end Elementary

end HilbertCrouzeix

end

end OAI
