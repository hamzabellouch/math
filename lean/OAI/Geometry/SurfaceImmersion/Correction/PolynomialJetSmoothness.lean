import OAI.Geometry.SurfaceImmersion.Correction.PolynomialJetRecursion

namespace OAI

/-! The finite correction expressions have coefficients smooth throughout
the admissible low-jet domain. No higher jets occur in coefficient inverses. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.MetricPolynomial
open CovarianceCorrector

lemma smooth_longitudinal {O : Set LowJet} {X₀ : LowJet → R4} {V : LowJet → C(Period, R4)}
    (hX : ContDiffOn ℝ ∞ X₀ O)
    (hV : ContDiffOn ℝ ∞ (fun z : LowJet × ℝ => V z.1 (z.2 : Period)) (O ×ˢ Set.univ)) :
    (longitudinal X₀ V).SmoothCoeffs O := by
  intro a
  let L : R4 →L[ℝ] ℝ := EuclideanSpace.proj a
  exact L.contDiff.comp_contDiffOn
    ((hX.comp contDiffOn_fst (fun _ hz => hz.1)).add hV)

lemma smooth_transverse {O : Set LowJet} {Y : LowJet → R4} (hY : ContDiffOn ℝ ∞ Y O) :
    (transverse Y).SmoothCoeffs O := by
  intro a
  let L : R4 →L[ℝ] ℝ := EuclideanSpace.proj a
  have hi : ContDiffOn ℝ ∞ (fun Q => Y Q a) O :=
    L.contDiff.comp_contDiffOn hY
  exact hi.comp contDiffOn_fst (fun _ hz => hz.1)

lemma smooth_initial {O : Set LowJet} (hO : IsOpen O) {V : LowJet → C(Period, R4)}
    (hV : ContDiffOn ℝ ∞ (fun z : LowJet × ℝ => V z.1 (z.2 : Period)) (O ×ˢ Set.univ)) :
    (initial V).SmoothCoeffs O := by
  intro a
  let L : R4 →L[ℝ] ℝ := EuclideanSpace.proj a
  have hc : (Expression.coeff (fun z => V z.1 (z.2 : Period) a)).SmoothCoeffs O :=
    L.contDiff.comp_contDiffOn hV
  exact Expression.smoothCoeffs_primitive hO (Expression.smoothCoeffs_fluct hO hc)

lemma smooth_step {O : Set LowJet} (hO : IsOpen O)
    {Y C X₀ : LowJet → R4} {V : LowJet → C(Period, R4)} {q : LowJet → ℝ}
    (hY : ContDiffOn ℝ ∞ Y O) (hC : ContDiffOn ℝ ∞ C O) (hX : ContDiffOn ℝ ∞ X₀ O)
    (hV : ContDiffOn ℝ ∞ (fun z : LowJet × ℝ => V z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (hd : ∀ Q ∈ O, PeriodicCorrector.gramDet (Y Q) (C Q) ≠ 0)
    (hq : ContDiffOn ℝ ∞ q O) (hqp : ∀ Q ∈ O, 0 < q Q)
    (hcircle : ∀ Q ∈ O, ∀ t, inner ℝ (V Q t) (V Q t) = q Q)
    {U : ℕ → VectorExpression} (hU : ∀ j, (U j).SmoothCoeffs O) (dx dy : Fin 2) (r : ℕ) :
    (step Y C X₀ V q dx dy U r).SmoothCoeffs O := by
  intro a
  apply Expression.smoothCoeffs_fullComponent hO hY hC hX hV hd hq hqp hcircle (EuclideanSpace.proj a) dy
  · exact Expression.smoothCoeffs_scale _ (Expression.smoothCoeffs_fluct hO
      (smooth_mixedForcing hO hU (smooth_longitudinal hX hV) (smooth_transverse hY) dx dy r))
  · exact Expression.smoothCoeffs_scale _ (Expression.smoothCoeffs_fluct hO (smooth_yyQuadratic hO hU dy (r + 1)))
  · exact Expression.smoothCoeffs_scale _ (Expression.smoothCoeffs_fluct hO
      (smooth_longitudinalForcing hO hU (smooth_longitudinal hX hV) dx r))

theorem coefficients_smooth {O : Set LowJet} (hO : IsOpen O)
    {Y C X₀ : LowJet → R4} {V : LowJet → C(Period, R4)} {q : LowJet → ℝ}
    (hY : ContDiffOn ℝ ∞ Y O) (hC : ContDiffOn ℝ ∞ C O) (hX : ContDiffOn ℝ ∞ X₀ O)
    (hV : ContDiffOn ℝ ∞ (fun z : LowJet × ℝ => V z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (hd : ∀ Q ∈ O, PeriodicCorrector.gramDet (Y Q) (C Q) ≠ 0)
    (hq : ContDiffOn ℝ ∞ q O) (hqp : ∀ Q ∈ O, 0 < q Q)
    (hcircle : ∀ Q ∈ O, ∀ t, inner ℝ (V Q t) (V Q t) = q Q)
    (dx dy : Fin 2) (n i : ℕ) :
    (coefficients Y C X₀ V q dx dy n i).SmoothCoeffs O := by
  induction n generalizing i with
  | zero => exact smooth_initial hO hV
  | succ n ih =>
    by_cases hi : i = n + 1
    · subst i
      rw [coefficients, Function.update_self]
      exact smooth_step hO hY hC hX hV hd hq hqp hcircle ih dx dy (n + 1)
    · rw [coefficients, Function.update_of_ne hi]
      exact ih i

end ClosedSurfaceR4.JetPolynomial.MetricPolynomial

end

end OAI
