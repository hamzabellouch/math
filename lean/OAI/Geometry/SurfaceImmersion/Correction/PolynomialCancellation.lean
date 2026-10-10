import OAI.Geometry.SurfaceImmersion.Correction.JetPolynomialScalar

namespace OAI

/-! Polynomial forcing gives a polynomial correction cancelling the actual
three metric fluctuations, with the support guarantee retained. -/
noncomputable section
open scoped ContDiff Topology
namespace ClosedSurfaceR4.JetPolynomial
open CovarianceCorrector LocalPeriodicExpansion

theorem exists_polynomial_cancellation {S : TopologicalSpace.Opens Base} {O : Set LowJet}
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
    {b c d : Expression} (hb : b.SmoothCoeffs O) (hc : c.SmoothCoeffs O) (hdp : d.SmoothCoeffs O)
    (bf cf df : Family S ℝ)
    (hbr : Expression.Represents G b bf) (hcr : Expression.Represents G c cf)
    (hdr : Expression.Represents G d df) :
    ∃ U : Family S R4,
      (∀ p ∈ S, average (U.val p) = 0) ∧
      (g.transverse.inner U.angle + bf).fluct = 0 ∧
      (g.longitudinal.inner U.angle + cf).fluct = 0 ∧
      ((2 : ℝ) • g.transverse.inner (U.slow (coordinateVector v)) + df).fluct = 0 ∧
      (∀ Z : Set Base, IsOpen Z → Z ⊆ S → (∀ p ∈ Z, bf.val p = 0) →
        (∀ p ∈ Z, cf.val p = 0) → (∀ p ∈ Z, df.val p = 0) → ∀ p ∈ Z, U.val p = 0) ∧
      VectorExpression.Represents G
        (fun i => Expression.fullComponent Y C X₀ V q (EuclideanSpace.proj i) v
          (b.fluct.scale (-1)) (d.fluct.scale (-1 / 2)) (c.fluct.scale (-1))) U := by
  have hmean (a : ℝ) (f : Family S ℝ) (p : Base) (_ : p ∈ S) :
      average ((a • f.fluct).val p) = 0 := by
    change average (fun t => a • f.fluct.val p t) = 0
    rw [average_const_smul, f.fluct_mean_zero, smul_zero]
  have hbs := Expression.smoothCoeffs_scale (-1) (Expression.smoothCoeffs_fluct hO hb)
  have hcs := Expression.smoothCoeffs_scale (-1) (Expression.smoothCoeffs_fluct hO hc)
  have hds := Expression.smoothCoeffs_scale (-1 / 2) (Expression.smoothCoeffs_fluct hO hdp)
  have hbr' := Expression.represents_scale (Expression.represents_fluct hO hQ hb hbr) (-1)
  have hcr' := Expression.represents_scale (Expression.represents_fluct hO hQ hc hcr) (-1)
  have hdr' := Expression.represents_scale (Expression.represents_fluct hO hQ hdp hdr) (-1 / 2)
  obtain ⟨U, hU0, hYf, hYs, hXf, hzero, hrep⟩ := exists_polynomial_system hO v g
    hY hC hX hV hd hq hqp hcircle hG hQ hYg hCg hXg hVg hqg hbs hds hcs
    ((-1 : ℝ) • bf.fluct) ((-1 / 2 : ℝ) • df.fluct) ((-1 : ℝ) • cf.fluct)
    hbr' hdr' hcr' (hmean _ _) (hmean _ _) (hmean _ _)
  refine ⟨U, hU0, ?_, ?_, ?_, ?_, hrep⟩
  · rw [Family.fluct_add, hYf, Family.fluct_smul, Family.fluct_fluct]
    module
  · rw [Family.fluct_add, hXf]
    module
  · rw [Family.fluct_add, Family.fluct_smul, hYs, Family.fluct_smul, Family.fluct_fluct]
    module
  · intro Z hZ hZS hbZ hcZ hdZ
    have hz (a : ℝ) (f : Family S ℝ) (hf : ∀ p ∈ Z, f.val p = 0) :
        ∀ p ∈ Z, (a • f.fluct).val p = 0 := by
      intro p hp
      change a • f.fluct.val p = 0
      rw [f.fluct_zero_at (hf p hp), smul_zero]
    exact hzero Z hZ hZS (hz _ _ hbZ) (hz _ _ hdZ) (hz _ _ hcZ)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
