import OAI.Analysis.KadisonKastler.ProductCentralizerSmallProjections
import OAI.Analysis.KadisonKastler.MinimalProjectionEquivalence

namespace OAI

/-! # Diffuseness of the fixed product-state centralizer

Scalar center and small nonzero projections exclude minimal projections.
This supplies the trace cuts used to assemble state-scaling isometries.
-/

namespace KadisonKastler

open Generator Generator.Tracial UltrapowerBridge

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem algebraProjection_trace_mono (τ : TracialRepresentation M)
    {p q : AlgebraProjection M} (h : p ≤ q) :
    (τ.trace p.val).re ≤ (τ.trace q.val).re := by
  have he := projection_trace_sq τ (q.val-p.val)
    (p.property.sub_of_mul_eq_right q.property h)
  rw [τ.trace_sub,Complex.sub_re] at he
  nlinarith [sq_nonneg (τ.norm₂ (q.val-p.val))]

theorem factor_no_minimal_of_small_projections (τ : TracialRepresentation M)
    (hM : ScalarCenter M)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ q : AlgebraProjection M,
      q.val ≠ 0 ∧ (τ.trace q.val).re < ε)
    (p : AlgebraProjection M) : ¬ IsMinimalProjectionIn M p := by
  intro hp
  obtain ⟨q,hq,hqt⟩ := hsmall _ (projection_trace_pos τ p.val p.property hp.1)
  obtain ⟨r,hrq,hr⟩ := factor_exists_minimal_below hM p hp q hq
  obtain ⟨v,hvp,hvr⟩ := factor_minimal_projections_equivalent hM p r hp hr
  have ht : τ.trace p.val=τ.trace r.val := by
    rw [← hvp,← hvr]
    exact v.trace_support_eq_target τ
  have hle := algebraProjection_trace_mono τ hrq
  rw [← ht] at hle
  exact (not_lt_of_ge hle) hqt

theorem diffuse_of_no_minimal
    (h : ∀ p : AlgebraProjection M, ¬ IsMinimalProjectionIn M p)
    (p : Algebra M) (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ q : Algebra M, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q := by
  classical
  by_contra hn
  apply h ⟨p,hp⟩
  refine ⟨hp0,?_⟩
  intro q hq
  by_cases hq0 : q.val=0
  · exact Or.inl hq0
  · right
    by_contra hqp
    apply hn
    exact ⟨q.val,q.property,hq0,(fun he => hqp (Subtype.ext he)),hq,
      projection_mul_of_le hq⟩

namespace PointedMatrixSites

variable {Ω : H} (S : PointedMatrixSites M Ω twoRatioSiteParameter)

include S

theorem twoRatio_centralizer_scalarCenter :
    ScalarCenter (stateCentralizerVonNeumann (M := M) Ω) := by
  have h := S.twoRatioStages.stateCentralizer_scalarCenter
  change ScalarCenter (stateCentralizerVonNeumann (M := S.twoRatioStages.algebra) Ω) at h
  simpa only [S.twoRatioStages_algebra] using h

theorem twoRatio_centralizer_diffuse
    (p : Algebra (stateCentralizerVonNeumann (M := M) Ω))
    (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ q : Algebra (stateCentralizerVonNeumann (M := M) Ω),
      IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q :=
  diffuse_of_no_minimal
    (factor_no_minimal_of_small_projections
      (stateCentralizerTrace Ω S.unit_vector S.separating)
      S.twoRatio_centralizer_scalarCenter S.exists_small_centralizer_projection) p hp hp0

end PointedMatrixSites

end

end KadisonKastler

end OAI
