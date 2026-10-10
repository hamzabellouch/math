import OAI.Geometry.SurfaceImmersion.Correction.PolynomialCorrectorSystem

namespace OAI

/-! The actual periodic system admits the polynomial solution whose order
bounds were established in JetPolynomialFullCorrector. -/
noncomputable section
open scoped ContDiff Topology

namespace ClosedSurfaceR4.JetPolynomial
open CovarianceCorrector LocalPeriodicExpansion

/-- The family solving the complete periodic system has the represented
four-coordinate correction. All equations and the zero-support property
are retained from the actual periodic solver. -/
theorem exists_polynomial_system {S : TopologicalSpace.Opens Base} {O : Set LowJet}
    (hO : IsOpen O) (v : Fin 2) (g : Geometry (E := R4) S (coordinateVector v))
    {Y C X₀ : LowJet → R4} {V : LowJet → C(Period, R4)} {q : LowJet → ℝ}
    (hY : ContDiffOn ℝ ∞ Y O) (hC : ContDiffOn ℝ ∞ C O) (hX : ContDiffOn ℝ ∞ X₀ O)
    (hV : ContDiffOn ℝ ∞ (fun z : LowJet × ℝ => V z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (hd : ∀ Q ∈ O, PeriodicCorrector.gramDet (Y Q) (C Q) ≠ 0)
    (hq : ContDiffOn ℝ ∞ q O) (hqp : ∀ Q ∈ O, 0 < q Q)
    (hcircle : ∀ Q ∈ O, ∀ t, inner ℝ (V Q t) (V Q t) = q Q)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) S O)
    (hYg : ∀ p ∈ S, g.Y p = Y (lowJet G p))
    (hCg : ∀ p ∈ S, g.C p = C (lowJet G p))
    (hXg : ∀ p ∈ S, g.X₀ p = X₀ (lowJet G p))
    (hVg : ∀ p ∈ S, g.V.val p = V (lowJet G p))
    (hqg : ∀ p ∈ S, g.q p = q (lowJet G p))
    {h j e : Expression} (hh : h.SmoothCoeffs O) (hj : j.SmoothCoeffs O) (he : e.SmoothCoeffs O)
    (hf jf ef : Family S ℝ)
    (hhr : ∀ p ∈ S, ∀ t : ℝ, h.eval G (p, t) = hf.val p (t : Period))
    (hjr : ∀ p ∈ S, ∀ t : ℝ, j.eval G (p, t) = jf.val p (t : Period))
    (her : ∀ p ∈ S, ∀ t : ℝ, e.eval G (p, t) = ef.val p (t : Period))
    (hh0 : ∀ p ∈ S, average (hf.val p) = 0)
    (hj0 : ∀ p ∈ S, average (jf.val p) = 0)
    (he0 : ∀ p ∈ S, average (ef.val p) = 0) :
    ∃ U : Family S R4,
      (∀ p ∈ S, average (U.val p) = 0) ∧
      g.transverse.inner U.angle = hf ∧
      g.transverse.inner (U.slow (coordinateVector v)) = jf ∧
      (g.longitudinal.inner U.angle).fluct = ef ∧
      (∀ Z : Set Base, IsOpen Z → Z ⊆ S → (∀ p ∈ Z, hf.val p = 0) →
        (∀ p ∈ Z, jf.val p = 0) → (∀ p ∈ Z, ef.val p = 0) → ∀ p ∈ Z, U.val p = 0) ∧
      VectorExpression.Represents G
        (fun i => Expression.fullComponent Y C X₀ V q (EuclideanSpace.proj i) v h j e) U := by
  obtain ⟨U, hU0, hUa, hUs, hUfl, hUz, hform⟩ := g.exists_system_formula hf jf ef hh0 hj0 he0
  refine ⟨U, hU0, hUa, hUs, hUfl, hUz, ?_⟩
  intro i p hp t
  rw [Expression.eval_fullComponent hO S.isOpen hY hC hX hV hd hq hqp hcircle
    (EuclideanSpace.proj i) v hh hj he hG hQ hf.val jf.val ef.val hhr hjr her hp]
  change (EuclideanSpace.proj i) (PeriodicCorrector.fullSolutionFormula (coordinateVector v)
    (fun x => Y (lowJet G x)) (fun x => C (lowJet G x)) (fun x => X₀ (lowJet G x))
    (fun x => V (lowJet G x)) (fun x => q (lowJet G x)) hf.val jf.val ef.val (p, t)) =
      (EuclideanSpace.proj i) (U.val p (t : Period))
  rw [hform p hp t]
  unfold PeriodicCorrector.fullSolutionFormula
  rw [hYg p hp, hCg p hp, hXg p hp, hVg p hp, hqg p hp]

end ClosedSurfaceR4.JetPolynomial

end

end OAI
