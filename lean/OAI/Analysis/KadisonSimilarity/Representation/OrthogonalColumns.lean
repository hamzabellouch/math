import OAI.Analysis.KadisonSimilarity.Representation.Amplification

namespace OAI

/-! Finite orthogonal word levels and their full-codomain errors. -/

noncomputable section
namespace KadisonSimilarity

open Finset ContinuousLinearMap

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- Assemble maps from the individual coordinates of a finite Hilbert sum. -/
def sumColumns {N : ℕ} (U : Fin N → H →L[ℂ] K) : HilbertCopies H N →L[ℂ] K :=
  ∑ i : Fin N, (U i).comp (PiLp.proj 2 (fun _ : Fin N => H) i)

@[simp] theorem sumColumns_apply {N : ℕ} (U : Fin N → H →L[ℂ] K)
    (x : HilbertCopies H N) : sumColumns U x = ∑ i : Fin N, U i (x i) := by
  simp [sumColumns]

/-- Pythagoras for the finite family of orthogonal output vectors. -/
theorem norm_sum_sq_of_pairwise_orthogonal {N : ℕ} (v : Fin N → K)
    (horth : ∀ i j, i ≠ j → inner ℂ (v i) (v j) = 0) :
    ‖∑ i : Fin N, v i‖ ^ 2 = ∑ i : Fin N, ‖v i‖ ^ 2 := by
  have hin (i : Fin N) : ∑ j : Fin N, inner ℂ (v j) (v i) = inner ℂ (v i) (v i) := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      exact horth j i hji
    · simp
  simp only [norm_sq_eq_re_inner (𝕜 := ℂ), sum_inner, inner_sum, hin, map_sum]

/-- Orthogonal output levels allow the same bound at every matrix size. -/
theorem norm_sumColumns_le {N : ℕ} (U : Fin N → H →L[ℂ] K) {c : ℝ}
    (hc : 0 ≤ c) (hU : ∀ i, ‖U i‖ ≤ c)
    (horth : ∀ i j, i ≠ j → ∀ x y, inner ℂ (U i x) (U j y) = 0) :
    ‖sumColumns U‖ ≤ c := by
  apply opNorm_le_bound _ hc
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).mp
  rw [sumColumns_apply, norm_sum_sq_of_pairwise_orthogonal _ (fun i j hij => horth i j hij _ _)]
  calc
    _ ≤ ∑ i : Fin N, (c * ‖x i‖) ^ 2 := by
      apply sum_le_sum
      intro i _
      exact pow_le_pow_left₀ (norm_nonneg _) ((U i).le_opNorm (x i) |>.trans
        (mul_le_mul_of_nonneg_right (hU i) (norm_nonneg _))) 2
    _ = (c * ‖x‖) ^ 2 := by
      simp_rw [mul_pow]
      rw [← mul_sum, ← PiLp.norm_sq_eq_of_L2, ← mul_pow]

variable [CompleteSpace H] [CompleteSpace K]

@[simp] theorem sumColumns_adjoint_apply {N : ℕ} (U : Fin N → H →L[ℂ] K)
    (y : K) (i : Fin N) : (sumColumns U).adjoint y i = (U i).adjoint y := by
  apply ext_inner_left ℂ
  intro x
  have h := adjoint_inner_right (sumColumns U) (PiLp.single 2 i x) y
  have hsum : sumColumns U (PiLp.single 2 i x) = U i x := by
    simp only [sumColumns_apply, PiLp.single_apply, apply_ite, map_zero]
    simp
  rw [hsum] at h
  have hin : inner ℂ (PiLp.single 2 i x) ((sumColumns U).adjoint y) =
      inner ℂ x ((sumColumns U).adjoint y i) := by
    rw [PiLp.inner_apply]
    have hs := Finset.sum_eq_single (s := Finset.univ) i
      (f := fun j : Fin N => inner ℂ
        ((PiLp.single 2 i x : HilbertCopies H N) j) ((sumColumns U).adjoint y j))
      (by intro j _ hji; simp [hji]) (by simp)
    simpa only [PiLp.single_eq_same] using hs
  rw [hin] at h
  exact h.trans (adjoint_inner_right (U i) x y).symm


/-- The block entries of the compressed operator are its coordinatewise
compressions along the word-level inclusions. -/
theorem sumColumns_compression {N : ℕ} (U : Fin N → H →L[ℂ] K) (T : K →L[ℂ] K) :
    (sumColumns U).adjoint.comp (T.comp (sumColumns U)) =
      matrixOperator (fun i j => (U i).adjoint.comp (T.comp (U j))) := by
  ext x i
  simp [sumColumns_apply, matrixOperator, map_sum]

omit [CompleteSpace H] [CompleteSpace K] in
/-- The full error of an assembled inclusion is the assembly of its level
errors. -/
theorem sumColumns_intertwining_error {N : ℕ} (U : Fin N → H →L[ℂ] K)
    (G : K →L[ℂ] K) (B : H →L[ℂ] H) :
    G.comp (sumColumns U) - (sumColumns U).comp (amplify B N) =
      sumColumns (fun i => G.comp (U i) - (U i).comp B) := by
  ext x
  simp [sumColumns_apply, map_sum, Finset.sum_sub_distrib]

/-- Adjoint and finite Hilbert amplification commute. -/
theorem adjoint_amplify (B : H →L[ℂ] H) (N : ℕ) :
    (amplify B N).adjoint = amplify B.adjoint N := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  simp only [adjoint_inner_right, PiLp.inner_apply, amplify_apply]

omit [CompleteSpace H] [CompleteSpace K] in
/-- The propagation estimate on individual orthogonal word levels gives a
full-codomain norm bound on their assembled inclusion. -/
theorem norm_word_inclusion_error_le {N : ℕ}
    (U : Fin N → H →L[ℂ] K) (L : Fin N → Submodule ℂ K)
    (hU : ∀ i x, U i x ∈ L i)
    (horth : ∀ i j, i ≠ j → ∀ x ∈ L i, ∀ y ∈ L j, inner ℂ x y = 0)
    (G : K →L[ℂ] K) (B : H →L[ℂ] H)
    (hG : ∀ i x, x ∈ L i → G x ∈ L i)
    {η : ℝ} (hη : 0 ≤ η)
    (herr : ∀ i, ‖G.comp (U i) - (U i).comp B‖ ≤ η) :
    ‖G.comp (sumColumns U) - (sumColumns U).comp (amplify B N)‖ ≤ η := by
  rw [sumColumns_intertwining_error]
  apply norm_sumColumns_le _ hη herr
  intro i j hij x y
  apply horth i j hij
  · exact (L i).sub_mem (hG i _ (hU i x)) (hU i (B x))
  · exact (L j).sub_mem (hG j _ (hU j y)) (hU j (B y))

end KadisonSimilarity

end

end OAI
