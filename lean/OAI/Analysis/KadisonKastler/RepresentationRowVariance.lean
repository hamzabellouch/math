import OAI.Analysis.KadisonKastler.RowRepresentationContraction

namespace OAI

/-! The exact loss of auxiliary Hilbert-space energy under a normalized row.
The formula records the intertwining error of the averaged right operator. -/

namespace KadisonKastler

noncomputable section

open scoped InnerProductSpace

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H}

theorem representationRowAverage_variance
    (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) {ι : Type*} [Fintype ι]
    (r : ι → Algebra M) (hr : ∑ i, r i * star (r i) = 1)
    (R : H →L[ℂ] K) (ξ : H) :
    (∑ i, ‖R ((star (r i) : H →L[ℂ] H) ξ) -
      (star (π (r i))) (representationRowAverage π r R ξ)‖ ^ 2) =
      (∑ i, ‖R ((star (r i) : H →L[ℂ] H) ξ)‖ ^ 2) -
        ‖representationRowAverage π r R ξ‖ ^ 2 := by
  let N : VonNeumannAlgebra K :=
    { toStarSubalgebra := ⊤
      centralizer_centralizer' := Set.Subset.antisymm (Set.subset_univ _)
        Set.subset_centralizer_centralizer }
  let s : ι → Algebra N := fun i => ⟨π (r i), by trivial⟩
  have hs : ∑ i, s i * star (s i) = 1 := by
    apply Subtype.ext
    have hπ : ∑ i, π (r i) * star (π (r i)) = 1 := by
      simpa only [map_sum, map_mul, map_star, map_one] using congrArg π hr
    simpa only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul,
      StarMemClass.coe_star, OneMemClass.coe_one, s, Subtype.coe_mk] using hπ
  let v : ι → K := fun i => R ((star (r i) : H →L[ℂ] H) ξ)
  have he : rowSynthesis s v = representationRowAverage π r R ξ := by
    simp [rowSynthesis, s, v, representationRowAverage]
  have h := normalizedRow_variance s hs v
  rw [he] at h
  simpa only [s, v, StarMemClass.coe_star, Subtype.coe_mk] using h

omit [CompleteSpace K] in
theorem representationRowAverage_inputEnergy_le
    {ι : Type*} [Fintype ι] (r : ι → Algebra M)
    (hr : ∑ i, r i * star (r i) = 1) (R : H →L[ℂ] K) (ξ : H) :
    (∑ i, ‖R ((star (r i) : H →L[ℂ] H) ξ)‖ ^ 2) ≤ ‖R‖ ^ 2 * ‖ξ‖ ^ 2 := by
  have hs : (∑ i, ‖(star (r i) : H →L[ℂ] H) ξ‖ ^ 2) = ‖ξ‖ ^ 2 := by
    have hξ : (inner ℂ ξ ξ).re = ‖ξ‖ ^ 2 := by
      simpa only [RCLike.re_eq_complex_re] using (norm_sq_eq_re_inner (𝕜 := ℂ) ξ).symm
    have h := rowAdjointVector_norm_sq r ξ
    rw [hr] at h
    simpa only [PiLp.norm_sq_eq_of_L2, rowAdjointVector, PiLp.toLp_apply,
      OneMemClass.coe_one, one_apply_eq_self, hξ] using h
  calc
    _ ≤ ∑ i, (‖R‖ * ‖(star (r i) : H →L[ℂ] H) ξ‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact pow_le_pow_left₀ (norm_nonneg _) (R.le_opNorm _) 2
    _ = _ := by simp only [mul_pow, ← Finset.mul_sum, hs]

theorem representationRowAverage_energy_and_defect_le
    (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) {ι : Type*} [Fintype ι]
    (r : ι → Algebra M) (hr : ∑ i, r i * star (r i) = 1)
    (R : H →L[ℂ] K) (ξ : H) :
    ‖representationRowAverage π r R ξ‖ ^ 2 +
      (∑ i, ‖R ((star (r i) : H →L[ℂ] H) ξ) -
        (star (π (r i))) (representationRowAverage π r R ξ)‖ ^ 2) ≤
      ‖R‖ ^ 2 * ‖ξ‖ ^ 2 := by
  rw [representationRowAverage_variance π r hr R ξ]
  linarith [representationRowAverage_inputEnergy_le r hr R ξ]

end

end KadisonKastler

end OAI
