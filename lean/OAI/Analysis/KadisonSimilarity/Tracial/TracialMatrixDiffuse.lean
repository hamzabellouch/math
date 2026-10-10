import OAI.Analysis.KadisonSimilarity.Tracial.TracialFactorComparison
import OAI.Analysis.KadisonSimilarity.Tracial.SmallTraceFrames

namespace OAI

/-! Arbitrarily small full-matrix corners and comparison split every
nonzero projection in the source algebra. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H)
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) G.trace G.vector)

include M in
/-- A nonzero projection contains a proper nonzero subprojection. -/
theorem proper_subprojection_of_matrix_tower
    (hf : Function.Injective G.vector)
    (comparison : FiniteFactorProjectionComparison (fun a => (G.trace a).re))
    (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop)
    (p : P) (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ q : P, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q := by
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
  obtain ⟨n, _, t, ht, htp, F, hF⟩ := M.exists_small_trace_frame hsize hppos
  have hFp : (G.trace F.corner).re ≤ (G.trace p).re := by
    rw [hF, Complex.ofReal_re]
    exact htp.le
  obtain ⟨v, hv, hpv⟩ := comparison p F.corner hp F.corner_projection hFp
  let q := v * star v
  have hq : IsStarProjection q := range_projection_of_initial_projection
    F.corner v F.corner_projection hv
  have hτq : G.trace q = (t : ℂ) := by
    change G.trace (v * star v) = _
    rw [G.tracial, hv, hF]
  have hq0 : q ≠ 0 := by
    intro h
    have hh := congrArg Complex.re hτq
    rw [h, map_zero] at hh
    simp only [Complex.zero_re, Complex.ofReal_re] at hh
    exact (ne_of_gt ht) hh.symm
  have hqp : q ≠ p := by
    intro h
    have hh := congrArg Complex.re hτq
    rw [h, Complex.ofReal_re] at hh
    exact (ne_of_lt htp) hh.symm
  refine ⟨q, hq, hq0, hqp, hpv, ?_⟩
  have hpq : p * q = q := hpv
  have h := congrArg star hpq
  simpa only [star_mul, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq] using h

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
