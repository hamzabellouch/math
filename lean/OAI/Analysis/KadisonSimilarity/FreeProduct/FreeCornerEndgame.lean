import OAI.Analysis.KadisonSimilarity.FreeProduct.HankelCommutator
import OAI.Analysis.KadisonSimilarity.Representation.OrthogonalColumns

namespace OAI

/-!
# The finite Fourier test completing the free-corner estimate

Given the actual finite word-level inclusion and its Fourier compression,
the two propagation errors, narrow-arc norm bound, and Hankel test imply the
paper's corner-independent constant. The free-product construction of those
data is not assumed to be a published theorem.
-/

noncomputable section
namespace KadisonSimilarity

open ContinuousLinearMap

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace H] in
/-- Scaling the test operator scales its commutator. -/
theorem commutator_smul_right (B S : H →L[ℂ] H) (c : ℂ) :
    commutator B (c • S) = c • commutator B S := by
  simp only [commutator, mul_smul_comm, smul_mul_assoc, smul_sub]

omit [CompleteSpace H] in
/-- Scalar multiplication of a bounded operator has the expected norm. -/
theorem norm_complex_smul_endomorphism (T : H →L[ℂ] H) (c : ℂ) :
    ‖c • T‖ = ‖c‖ * ‖T‖ := norm_smul c T

/-- A finite Fourier compression suffices to finish the corner estimate.
All assumptions describe constructed operators and their checked identities;
none assumes the free-corner conclusion. -/
theorem free_corner_bound_of_fourier_compression
    {N : ℕ} (hN : 0 < N) (G T : H →L[ℂ] H) (B S : K →L[ℂ] K)
    (ι : HilbertCopies K N →L[ℂ] H)
    (toeplitz : Matrix (Fin N) (Fin N) ℝ)
    {u ε c₀ : ℝ} (hu : 0 < u) (hε : 0 ≤ ε) (hc₀ : 0 ≤ c₀)
    (hι : ‖ι‖ ≤ 1) (hT : ‖T‖ ≤ 3 * u)
    (hG : ‖commutator G T‖ ≤ ε * ‖T‖)
    (hR : ‖G.comp ι - ι.comp (amplify B N)‖ ≤ 2 * c₀ * ε)
    (hR' : ‖G.adjoint.comp ι - ι.comp (amplify B N).adjoint‖ ≤ 2 * c₀ * ε)
    (hfourier : ι.adjoint.comp (T.comp ι) =
      (u : ℂ) • matrixOperator (fun i j =>
        (toeplitz i j : ℂ) • ContinuousLinearMap.id ℂ K +
          (arcHankelMatrix N i j : ℂ) • S)) :
    ‖commutator B S‖ ≤ 6 * Real.pi ^ 2 * (1 + 4 * c₀) * ε := by
  let X : Matrix (Fin N) (Fin N) (K →L[ℂ] K) := fun i j =>
    (toeplitz i j : ℂ) • ContinuousLinearMap.id ℂ K +
      (arcHankelMatrix N i j : ℂ) • S
  have hlower := norm_commutator_fourier_matrix_lower hN B S toeplitz
  change (1 / Real.pi ^ 2) * ‖commutator B S‖ ≤
    ‖commutator (amplify B N) (matrixOperator X)‖ at hlower
  have hupper := norm_compressed_commutator_le_paper G T (amplify B N) ι hι hG hR hR'
  have hscaled : ‖commutator (amplify B N) (ι.adjoint.comp (T.comp ι))‖ =
      u * ‖commutator (amplify B N) (matrixOperator X)‖ := by
    have hf : ι.adjoint.comp (T.comp ι) = (u : ℂ) • matrixOperator X := hfourier
    rw [hf, commutator_smul_right]
    have hs : ‖(u : ℂ) • commutator (amplify B N) (matrixOperator X)‖ =
        ‖(u : ℂ)‖ * ‖commutator (amplify B N) (matrixOperator X)‖ :=
      norm_complex_smul_endomorphism _ (u : ℂ)
    rw [hs, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
  rw [hscaled] at hupper
  apply cancel_corner_trace hu
  have hhalf : 1 / (2 * Real.pi ^ 2) ≤ 1 / Real.pi ^ 2 := by
    apply one_div_le_one_div_of_le (sq_pos_of_pos Real.pi_pos)
    nlinarith [sq_nonneg Real.pi]
  calc
    u / (2 * Real.pi ^ 2) * ‖commutator B S‖ =
        u * ((1 / (2 * Real.pi ^ 2)) * ‖commutator B S‖) := by ring
    _ ≤ u * ((1 / Real.pi ^ 2) * ‖commutator B S‖) := by gcongr
    _ ≤ u * ‖commutator (amplify B N) (matrixOperator X)‖ :=
      mul_le_mul_of_nonneg_left hlower hu.le
    _ ≤ (1 + 4 * c₀) * ε * ‖T‖ := hupper
    _ ≤ (1 + 4 * c₀) * ε * (3 * u) := by gcongr
    _ = 3 * u * (1 + 4 * c₀) * ε := by ring

/-- The word-level hypotheses of propagation imply the complete finite Fourier
endgame, including both full-codomain errors. -/
theorem free_corner_bound_of_word_levels
    {N : ℕ} (hN : 0 < N) (G T : H →L[ℂ] H) (B S : K →L[ℂ] K)
    (U : Fin N → K →L[ℂ] H) (L : Fin N → Submodule ℂ H)
    (hUnorm : ∀ i, ‖U i‖ ≤ 1) (hUlevel : ∀ i x, U i x ∈ L i)
    (horth : ∀ i j, i ≠ j → ∀ x ∈ L i, ∀ y ∈ L j, inner ℂ x y = 0)
    (hGlevel : ∀ i x, x ∈ L i → G x ∈ L i)
    (hGstarlevel : ∀ i x, x ∈ L i → G.adjoint x ∈ L i)
    (toeplitz : Matrix (Fin N) (Fin N) ℝ)
    {u ε c₀ : ℝ} (hu : 0 < u) (hε : 0 ≤ ε) (hc₀ : 0 ≤ c₀)
    (hT : ‖T‖ ≤ 3 * u) (hG : ‖commutator G T‖ ≤ ε * ‖T‖)
    (herr : ∀ i, ‖G.comp (U i) - (U i).comp B‖ ≤ 2 * c₀ * ε)
    (herr' : ∀ i, ‖G.adjoint.comp (U i) - (U i).comp B.adjoint‖ ≤ 2 * c₀ * ε)
    (hfourier : (sumColumns U).adjoint.comp (T.comp (sumColumns U)) =
      (u : ℂ) • matrixOperator (fun i j =>
        (toeplitz i j : ℂ) • ContinuousLinearMap.id ℂ K +
          (arcHankelMatrix N i j : ℂ) • S)) :
    ‖commutator B S‖ ≤ 6 * Real.pi ^ 2 * (1 + 4 * c₀) * ε := by
  have hι : ‖sumColumns U‖ ≤ 1 := norm_sumColumns_le U (by norm_num) hUnorm
    (fun i j hij x y => horth i j hij _ (hUlevel i x) _ (hUlevel j y))
  have hη : 0 ≤ 2 * c₀ * ε := by positivity
  have hR := norm_word_inclusion_error_le U L hUlevel horth G B hGlevel hη herr
  have hR' := norm_word_inclusion_error_le U L hUlevel horth G.adjoint B.adjoint
    hGstarlevel hη herr'
  rw [← adjoint_amplify] at hR'
  exact free_corner_bound_of_fourier_compression hN G T B S (sumColumns U)
    toeplitz hu hε hc₀ hι hT hG hR hR' hfourier

end KadisonSimilarity

end

end OAI
