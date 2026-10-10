import Mathlib
import OAI.Analysis.Crouzeix.NumericalRange

namespace OAI

/-! Exact polynomial compression on spans of finitely many operator iterates. -/

noncomputable section

open scoped TensorProduct Matrix.Norms.L2Operator InnerProductSpace

open Set

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def compression (A : Operator H) (E : Submodule ℂ H) [E.HasOrthogonalProjection] :
    Operator E := E.orthogonalProjectionOnto.comp (A.comp E.subtypeL)

theorem compression_inner (A : Operator H) (E : Submodule ℂ H)
    [E.HasOrthogonalProjection] (x : E) :
    ⟪x, compression A E x⟫_ℂ = ⟪(x : H), A (x : H)⟫_ℂ :=
  Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left x (A x)

theorem numericalRange_compression_subset (A : Operator H) (E : Submodule ℂ H)
    [E.HasOrthogonalProjection] : numericalRange (compression A E) ⊆ numericalRange A := by
  rintro z ⟨x, hx, hz⟩
  exact ⟨(x : H), hx, (compression_inner A E x).symm.trans hz⟩

theorem coe_compression_apply (A : Operator H) (E : Submodule ℂ H)
    [E.HasOrthogonalProjection] (x : E) (hx : A (x : H) ∈ E) :
    (compression A E x : H) = A (x : H) := by
  have hh := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (⟨A x, hx⟩ : E)
  exact congrArg (fun v : E => (v : H)) hh

theorem coe_compression_pow (A : Operator H) (E : Submodule ℂ H)
    [E.HasOrthogonalProjection] (x : E) (k : ℕ)
    (hx : ∀ j : ℕ, j ≤ k → (A ^ j) (x : H) ∈ E) :
    (((compression A E) ^ k) x : H) = (A ^ k) (x : H) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk := ih (fun j hj => hx j (hj.trans (Nat.le_succ k)))
    have hmem : A (((compression A E) ^ k) x : H) ∈ E := by
      rw [hk]
      simpa only [pow_succ', mul_apply_eq_comp] using hx (k + 1) le_rfl
    simpa only [pow_succ', mul_apply_eq_comp] using
      (coe_compression_apply A E (((compression A E) ^ k) x) hmem).trans (congrArg A hk)

def iterateSpan (A : Operator H) (d : ℕ) {l : ℕ} (ξ : Fin l → H) : Submodule ℂ H :=
  Submodule.span ℂ (Set.range (fun p : Fin (d + 1) × Fin l => (A ^ (p.1 : ℕ)) (ξ p.2)))

instance iterateSpanFiniteDimensional (A : Operator H) (d : ℕ) {l : ℕ} (ξ : Fin l → H) :
    FiniteDimensional ℂ (iterateSpan A d ξ) :=
  FiniteDimensional.span_of_finite ℂ (Set.finite_range _)

theorem iterate_mem_iterateSpan (A : Operator H) (d : ℕ) {l : ℕ} (ξ : Fin l → H)
    (j : Fin l) (k : ℕ) (hk : k ≤ d) : (A ^ k) (ξ j) ∈ iterateSpan A d ξ := by
  apply Submodule.subset_span
  exact ⟨(⟨k, Nat.lt_succ_of_le hk⟩, j), rfl⟩

theorem mem_iterateSpan (A : Operator H) (d : ℕ) {l : ℕ} (ξ : Fin l → H)
    (j : Fin l) : ξ j ∈ iterateSpan A d ξ := by
  simpa using iterate_mem_iterateSpan A d ξ j 0 (Nat.zero_le _)

def amplificationInclusion (E : Submodule ℂ H) (m : ℕ) :
    Amplification E m →L[ℂ] Amplification H m :=
  (TensorProduct.mapL E.subtypeL (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin m)))).completion

theorem norm_amplificationInclusion (E : Submodule ℂ H) (m : ℕ)
    (x : Amplification E m) : ‖amplificationInclusion E m x‖ = ‖x‖ := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (amplificationInclusion E m).continuous.norm continuous_norm) ?_
  intro a
  simp only [amplificationInclusion, ContinuousLinearMap.completion_apply_coe,
    UniformSpace.Completion.norm_coe]
  rw [TensorProduct.mapL_apply]
  change ‖TensorProduct.map E.subtypeₗᵢ.toLinearMap
    (LinearIsometry.id : EuclideanSpace ℂ (Fin m) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)).toLinearMap a‖ = ‖a‖
  exact (TensorProduct.mapIsometry E.subtypeₗᵢ (LinearIsometry.id :
    EuclideanSpace ℂ (Fin m) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m))).norm_map a

@[simp]
theorem amplificationInclusion_tmul (E : Submodule ℂ H) {m : ℕ}
    (x : E) (y : EuclideanSpace ℂ (Fin m)) :
    amplificationInclusion E m (↑(x ⊗ₜ[ℂ] y)) =
      (↑((x : H) ⊗ₜ[ℂ] y) : Amplification H m) := by
  simp [amplificationInclusion, ContinuousLinearMap.completion_apply_coe]

theorem polynomialEval_tmul (A : Operator H) {m d : ℕ} (B : Fin (d + 1) → Coeff m)
    (x : H) (y : EuclideanSpace ℂ (Fin m)) :
    polynomialEval A B (↑(x ⊗ₜ[ℂ] y)) =
      ∑ k : Fin (d + 1), (↑(((A ^ (k : ℕ)) x) ⊗ₜ[ℂ]
        (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin m) (B k) y)) : Amplification H m) := by
  simp only [polynomialEval, sum_apply, tensorOperator,
    ContinuousLinearMap.completion_apply_coe, TensorProduct.mapL_tmul]

theorem polynomial_compression_tmul (A : Operator H) (E : Submodule ℂ H)
    [E.HasOrthogonalProjection] {m d : ℕ} (B : Fin (d + 1) → Coeff m)
    (x : E) (y : EuclideanSpace ℂ (Fin m))
    (hx : ∀ j : ℕ, j ≤ d → (A ^ j) (x : H) ∈ E) :
    polynomialEval A B (amplificationInclusion E m (↑(x ⊗ₜ[ℂ] y))) =
      amplificationInclusion E m (polynomialEval (compression A E) B (↑(x ⊗ₜ[ℂ] y))) := by
  simp only [amplificationInclusion_tmul, polynomialEval_tmul, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [coe_compression_pow A E x k (fun j hj => hx j (hj.trans (Nat.le_of_lt_succ k.isLt)))]

theorem completion_coe_finsetSum {V : Type*} [NormedAddCommGroup V]
    {ι : Type*} (s : Finset ι) (f : ι → V) :
    (↑(∑ i ∈ s, f i) : UniformSpace.Completion V) =
      ∑ i ∈ s, (↑(f i) : UniformSpace.Completion V) :=
  map_sum (UniformSpace.Completion.toCompl : V →+ UniformSpace.Completion V) f s

theorem polynomial_bound_of_finite_compressions (A : Operator H)
    {m d : ℕ} (B : Fin (d + 1) → Coeff m) {C : ℝ} (hC : 0 ≤ C)
    (hfin : ∀ (E : Submodule ℂ H) [FiniteDimensional ℂ E],
      ‖polynomialEval (compression A E) B‖ ≤ C) :
    ‖polynomialEval A B‖ ≤ C := by
  apply (polynomialEval A B).opNorm_le_bound hC
  intro x
  refine UniformSpace.Completion.induction_on x
    (isClosed_le (polynomialEval A B).continuous.norm (continuous_const.mul continuous_norm)) ?_
  intro a
  obtain ⟨l, ξ, η, ha⟩ := TensorProduct.exists_sum_tmul_eq a
  let E := iterateSpan A d ξ
  let xE (j : Fin l) : E := ⟨ξ j, mem_iterateSpan A d ξ j⟩
  let v : Amplification E m := ∑ j : Fin l, (↑(xE j ⊗ₜ[ℂ] η j) : Amplification E m)
  have hav : (↑a : Amplification H m) = amplificationInclusion E m v := by
    rw [ha, completion_coe_finsetSum]
    simp only [v, map_sum, amplificationInclusion_tmul]
    rfl
  have hinter : polynomialEval A B (amplificationInclusion E m v) =
      amplificationInclusion E m (polynomialEval (compression A E) B v) := by
    simp only [v, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply polynomial_compression_tmul
    intro k hk
    exact iterate_mem_iterateSpan A d ξ j k hk
  calc
    ‖polynomialEval A B (↑a)‖ =
        ‖amplificationInclusion E m (polynomialEval (compression A E) B v)‖ := by
      rw [hav, hinter]
    _ = ‖polynomialEval (compression A E) B v‖ := norm_amplificationInclusion E m _
    _ ≤ ‖polynomialEval (compression A E) B‖ * ‖v‖ :=
      (polynomialEval (compression A E) B).le_opNorm v
    _ ≤ C * ‖v‖ := mul_le_mul_of_nonneg_right (hfin E) (norm_nonneg _)
    _ = C * ‖(↑a : Amplification H m)‖ := by rw [hav, norm_amplificationInclusion]

theorem polynomial_inequality_of_finite_compressions (A : Operator H)
    {m d : ℕ} (B : Fin (d + 1) → Coeff m)
    (hfin : ∀ (E : Submodule ℂ H) [FiniteDimensional ℂ E],
      ‖polynomialEval (compression A E) B‖ ≤
        2 * supNorm (numericalRange (compression A E)) (matrixPolynomial B)) :
    ‖polynomialEval A B‖ ≤ 2 * supNorm (numericalRange A) (matrixPolynomial B) := by
  have hbK := supNorm_bddAbove (isCompact_numericalClosure A)
    (continuous_matrixPolynomial B).continuousOn
  have hbW : BddAbove (insert 0 ((fun z => ‖matrixPolynomial B z‖) '' numericalRange A)) :=
    hbK.mono (Set.insert_subset_insert (Set.image_mono subset_closure))
  apply polynomial_bound_of_finite_compressions A B
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (supNorm_nonneg hbW))
  intro E _
  exact (hfin E).trans (mul_le_mul_of_nonneg_left
    (supNorm_mono (numericalRange_compression_subset A E) hbW) (by norm_num))

end CrouzeixHilbert
end

end OAI
