import OAI.Analysis.KadisonSimilarity.Tracial.TracialMatrixDiffuse

namespace OAI

/-! Projection comparison and small diagonal matrix corners show that each
finite matrix amplification of the prescribed source is diffuse. -/

noncomputable section
namespace KadisonSimilarity
open UltrapowerBridge
open scoped ComplexOrder

namespace TracialCornerGeometry
variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry A H)

theorem proper_subprojection_of_small_trace
    (hf : Function.Injective G.vector)
    (comparison : FiniteFactorProjectionComparison (fun a => (G.trace a).re))
    (small : ∀ s : ℝ, 0 < s → ∃ e : A, IsStarProjection e ∧
      0 < (G.trace e).re ∧ (G.trace e).re < s)
    (p : A) (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ q : A, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q := by
  have hv : G.vector p ≠ 0 := by
    intro h
    exact hp0 (hf (h.trans (map_zero G.vector).symm))
  have hpnorm : ‖G.vector p‖ ^ 2 = (G.trace p).re := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), G.inner_vector,
      hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]
    rfl
  have hppos : 0 < (G.trace p).re := by
    rw [← hpnorm]
    exact sq_pos_of_pos (norm_pos_iff.mpr hv)
  obtain ⟨e, he, hepos, hetrace⟩ := small _ hppos
  obtain ⟨v, hv, hpv⟩ := comparison p e hp he hetrace.le
  let q := v * star v
  have hq : IsStarProjection q := range_projection_of_initial_projection e v he hv
  have hτq : G.trace q = G.trace e := by
    change G.trace (v * star v) = _
    rw [G.tracial, hv]
  have hq0 : q ≠ 0 := by
    intro h
    have hh := congrArg Complex.re hτq
    rw [h, map_zero] at hh
    exact (ne_of_gt hepos) hh.symm
  have hqp : q ≠ p := by
    intro h
    have hh := congrArg Complex.re hτq
    rw [h] at hh
    exact (ne_of_lt hetrace) hh.symm
  refine ⟨q, hq, hq0, hqp, hpv, ?_⟩
  have hpq : p * q = q := hpv
  have h := congrArg star hpq
  simpa only [star_mul, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq] using h
end TracialCornerGeometry

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1) (tr : ∀ a b, τ (a * b) = τ (b * a))
  (hf : ∀ a, τ (star a * a) = 0 → a = 0)
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) τ.toLinearMap (gnsTracialVector τ))
  (hnormal : τ.gnsStarAlgHom.range =
    (representationVonNeumannAlgebra τ.gnsStarAlgHom).toStarSubalgebra)
  (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop)

include h1 tr hf M hnormal hsize in
theorem matrix_diffuse_of_tower (n : ℕ) [NeZero n]
    (p : CStarMatrix (Fin n) (Fin n) A) (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ q, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q := by
  let τn := normalizedMatrixTrace τ n
  let G := gnsTracialGeometry τn (normalizedMatrixTrace_tracial τ tr)
  apply G.proper_subprojection_of_small_trace
    (gnsTracialVector_injective τn (normalizedMatrixTrace_faithful τ hf))
    (matrix_projectionComparison_of_tower τ h1 tr hf M hnormal n) ?_ p hp hp0
  intro s hs
  obtain ⟨m, _, t, ht, hts, F, hF⟩ := M.exists_small_trace_frame hsize hs
  change τ F.corner = (t : ℂ) at hF
  refine ⟨matrixDiagonalHom n F.corner, F.corner_projection.map (matrixDiagonalHom n), ?_, ?_⟩
  · change 0 < (τn (matrixDiagonalHom n F.corner)).re
    rw [normalizedMatrixTrace_diagonal, hF, Complex.ofReal_re]
    exact ht
  · change (τn (matrixDiagonalHom n F.corner)).re < s
    rw [normalizedMatrixTrace_diagonal, hF, Complex.ofReal_re]
    exact hts

end KadisonSimilarity

end

end OAI
