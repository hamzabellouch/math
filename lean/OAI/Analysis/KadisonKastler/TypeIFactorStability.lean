import OAI.Analysis.KadisonKastler.PublishedTypeIInjectivity
import OAI.Analysis.KadisonKastler.InjectiveStability
import OAI.Analysis.KadisonKastler.TypeIEmbedding

namespace OAI

/-! # The type I branch and the projection dichotomy

The diffuse predicate is exactly the projection clause of
`Generator.IsII1Factor` and `TypeIIInfinityFactor`. Its alternative, for
a scalar-center algebra, is the existence of a minimal projection. This
dichotomy is proved directly. The separable type I branch uses the constructed
finite-group embedding.
-/

namespace KadisonKastler

open Generator.Tracial

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The diffuseness condition, independent of a finite
or semifinite factor structure. -/
def ProjectionDiffuse (M : VonNeumannAlgebra H) : Prop :=
  ∀ p : Algebra M, IsStarProjection p → p ≠ 0 →
    ∃ q : Algebra M, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q

theorem IsTypeIFactor.not_projectionDiffuse {M : VonNeumannAlgebra H}
    (hM : IsTypeIFactor M) : ¬ ProjectionDiffuse M := by
  intro hdiff
  obtain ⟨p, hp, hmin⟩ := hM.minimal
  obtain ⟨q, hq, hq0, hqp, hpq, _⟩ := hdiff p.val p.property hp
  rcases hmin ⟨q, hq⟩ hpq with hzero | heq
  · exact hq0 hzero
  · exact hqp (congrArg Subtype.val heq)

/-- A factor either has a minimal projection or every nonzero projection
has a proper nonzero subprojection. No spectral or classification input
is used in this alternative. -/
theorem isTypeIFactor_or_projectionDiffuse {M : VonNeumannAlgebra H}
    (hM : ScalarCenter M) : IsTypeIFactor M ∨ ProjectionDiffuse M := by
  classical
  by_cases htype : IsTypeIFactor M
  · exact Or.inl htype
  right
  intro p hp hp0
  by_contra hnone
  apply htype
  refine ⟨hM, ⟨⟨p, hp⟩, hp0, ?_⟩⟩
  intro q hqp
  by_cases hq0 : q.val = 0
  · exact Or.inl hq0
  right
  apply Subtype.ext
  by_contra hne
  apply hnone
  exact ⟨q.val, q.property, hq0, hne, hqp, projection_mul_of_le hqp⟩

theorem isTypeIFactor_iff_not_projectionDiffuse {M : VonNeumannAlgebra H}
    (hM : ScalarCenter M) : IsTypeIFactor M ↔ ¬ ProjectionDiffuse M := by
  constructor
  · exact IsTypeIFactor.not_projectionDiffuse
  · intro h
    exact (isTypeIFactor_or_projectionDiffuse hM).resolve_right h

/-- A nonzero finite factor without minimal projections is a II₁ factor.
Finiteness is only assumed for its identity
projection; the required isometry condition follows directly. -/
theorem isII1Factor_of_finite_of_not_typeI {M : VonNeumannAlgebra H}
    (hM : ScalarCenter M) (hnonzero : (0 : H →L[ℂ] H) ≠ 1)
    (hfinite : FiniteProjectionIn M 1) (htype : ¬ IsTypeIFactor M) :
    Generator.IsII1Factor M.toStarSubalgebra := by
  refine {
    nonzero := hnonzero
    weaklyClosed := Generator.Tracial.vonNeumann_wotClosed M
    factor := ?_
    finite := fun v hv => hfinite v hv (one_mul v)
    diffuse := (isTypeIFactor_or_projectionDiffuse hM).resolve_left htype }
  intro x hx
  obtain ⟨z, hz⟩ := hM x.val x.property (fun y hy =>
    congrArg Subtype.val (hx ⟨y, hy⟩))
  refine ⟨z, ?_⟩
  rw [Algebra.algebraMap_eq_smul_one]
  apply Subtype.ext
  exact hz

/-- The type I tolerance is independent of both the representation and
the algebras, under one-sided embedding and type I injectivity. -/
theorem uniform_typeI_strong_stability {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
      PublishedAmenableEmbedding (H := H) → PublishedTypeIInjectivity (H := H) →
      ∀ M N : VonNeumannAlgebra H, IsTypeIFactor M → kkDistance M N < δ →
        NearConjugacy M N ε := by
  obtain ⟨δ, hδ, hstable⟩ := uniform_injective_strong_stability.{u} hε
  refine ⟨δ, hδ, ?_⟩
  intro H _ _ _ hemb hinj M N hM hgap
  exact hstable H hemb M N (hinj M hM) hgap


/-- Type I stability on separable Hilbert spaces has a uniform tolerance. -/
theorem uniform_separable_typeI_strong_stability {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        [TopologicalSpace.SeparableSpace H],
      ∀ M N : VonNeumannAlgebra H, IsTypeIFactor M → kkDistance M N < δ →
        NearConjugacy M N ε := by
  refine ⟨min (1 / 2000) (ε / 300), lt_min (by norm_num) (by positivity), ?_⟩
  intro H _ _ _ _ M N hM hgap
  have hγ : 0 ≤ min (1 / 2000 : ℝ) (ε / 300) := by positivity
  obtain ⟨w, hw, hn⟩ := exists_unitary_typeI_embedding hM hγ
    ((min_le_left _ _).trans (by norm_num)) (nearInclusion_of_kkDistance_lt hgap)
  let P := unitaryConjugateAlgebra w M
  have hPN : P ≤ N := by
    rintro _ ⟨x, hx, rfl⟩
    exact hw x hx
  have hd := kkDistance_conjugate_le (M := N) (conjugates_unitaryConjugateAlgebra w M)
  rw [kkDistance_comm N (unitaryConjugateAlgebra w M), kkDistance_comm N M] at hd
  have hsmall := min_le_left (1 / 2000 : ℝ) (ε / 300)
  have hdist : kkDistance P N < 1 := by dsimp [P]; linarith
  have heq := eq_of_le_of_kkDistance_lt_one hPN hdist
  refine ⟨w, heq ▸ conjugates_unitaryConjugateAlgebra w M, ?_⟩
  have hε' := min_le_right (1 / 2000 : ℝ) (ε / 300)
  linarith

end KadisonKastler

end OAI
