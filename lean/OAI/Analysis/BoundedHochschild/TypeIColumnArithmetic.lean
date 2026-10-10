import OAI.Analysis.BoundedHochschild.CentralColumnCuts

namespace OAI

/-! Finite orthogonal column arithmetic for the type I decomposition. -/

noncomputable section

open scoped ComplexOrder BigOperators

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  {n : ℕ} {p : M}

omit [PartialOrder M] [StarOrderedRing M] in
lemma column_sum_projection (v : Fin n → PartialIso M)
    (ho : ∀ i j, i ≠ j → (v i).final * (v j).final = 0) :
    IsStarProjection (∑ i, (v i).final) :=
  orthogonal_projection_finset_sum (fun i => (v i).final) (fun i => (v i).final_proj)
    ho Finset.univ

omit [PartialOrder M] [StarOrderedRing M] in
lemma column_mul_residual (v : Fin n → PartialIso M)
    (ho : ∀ i j, i ≠ j → (v i).final * (v j).final = 0) (i : Fin n) :
    (v i).final * (1 - ∑ j, (v j).final) = 0 := by
  classical
  rw [mul_sub, mul_one, Finset.mul_sum, Finset.sum_eq_single i]
  · rw [(v i).final_proj.isIdempotentElem.eq, sub_self]
  · intro j _ hji
    exact ho i j hji.symm
  · simp

omit [PartialOrder M] [StarOrderedRing M] in
lemma exists_append_columns (v : Fin n → PartialIso M)
    (hi : ∀ i, (v i).initial = p)
    (ho : ∀ i j, i ≠ j → (v i).final * (v j).final = 0)
    (w : PartialIso M) (hwi : w.initial = p)
    (hwo : ∀ i, (v i).final * w.final = 0) :
    ∃ u : Fin (n + 1) → PartialIso M,
      (∀ i, (u i).initial = p) ∧
      (∀ i j, i ≠ j → (u i).final * (u j).final = 0) ∧
      (∑ i, (u i).final) = w.final + ∑ i, (v i).final := by
  let u : Fin (n + 1) → PartialIso M := Fin.cons w v
  refine ⟨u, ?_, ?_, ?_⟩
  · intro i
    exact Fin.cases hwi hi i
  · intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · intro h
      exact (h rfl).elim
    · intro _
      exact PartialIso.orthogonal_final_symm (hwo j)
    · intro _
      exact hwo i
    · intro h
      exact ho i j (fun he => h (congrArg Fin.succ he))
  · simp only [u, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

lemma column_count_trace_le (τ : M →ₚ[ℂ] ℂ)
    (htr : ∀ a b : M, τ (a * b) = τ (b * a))
    (v : Fin n → PartialIso M) (hi : ∀ i, (v i).initial = p)
    (ho : ∀ i j, i ≠ j → (v i).final * (v j).final = 0) :
    (n : ℝ) * (τ p).re ≤ (τ 1).re := by
  have ht (i : Fin n) : τ (v i).final = τ p := by
    change τ ((v i : M) * star (v i : M)) = τ p
    rw [htr]
    exact congrArg τ (hi i)
  have h := Complex.re_le_re (τ.monotone (column_sum_projection v ho).le_one)
  change (τ.toLinearMap (∑ i, (v i).final)).re ≤ (τ 1).re at h
  rw [map_sum] at h
  change Complex.reCLM (∑ i, τ (v i).final) ≤ (τ 1).re at h
  rw [map_sum] at h
  simpa only [ht, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Complex.reCLM_apply] using h

end KadisonRingrose
end BoundedHochschild

end

end OAI
