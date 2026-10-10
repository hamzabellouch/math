import OAI.Geometry.SurfaceImmersion.Correction.PolynomialAdvance

namespace OAI

/-! Finite smooth metric-cancelling coefficients with actual coordinate-jet
polynomial representations and the original support guarantee. -/
noncomputable section
open scoped ContDiff Topology
namespace ClosedSurfaceR4.JetPolynomial
open CovarianceCorrector LocalPeriodicExpansion

theorem exists_polynomial_coefficients {S : TopologicalSpace.Opens Base} {O : Set LowJet}
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
    (dxIndex : Fin 2) (n : ℕ) :
    ∃ U : ℕ → Family S R4,
      U 0 = g.initial ∧ (∀ i p, p ∈ S → average ((U i).val p) = 0) ∧
      (g.yyCoefficient U 1).fluct = 0 ∧
      (∀ Z : Set Base, IsOpen Z → Z ⊆ S → (∀ p ∈ Z, g.initial.val p = 0) →
        ∀ i p, p ∈ Z → (U i).val p = 0) ∧
      (∀ r, 1 ≤ r → r ≤ n →
        (g.xxCoefficient (coordinateVector dxIndex) U r).fluct = 0 ∧
        (g.xyCoefficient (coordinateVector dxIndex) U r).fluct = 0 ∧
        (g.yyCoefficient U (r + 1)).fluct = 0) ∧
      (∀ i, VectorExpression.Represents G
        (MetricPolynomial.coefficients Y C X₀ V q dxIndex v n i) (U i)) := by
  induction n with
  | zero =>
    refine ⟨fun _ => g.initial, rfl, fun _ _ hp => g.initial_mean_zero hp, ?_, ?_, ?_, ?_⟩
    · have hz : g.yyCoefficient (fun _ => g.initial) 1 = 0 := by
        simp only [Geometry.yyCoefficient, yCoefficient, yyQuadratic,
          Finset.Ico_self, Finset.sum_empty, g.initial_transverse_derivative, smul_zero, add_zero]
      rw [hz]
      ext p hp t
      simp only [Family.fluct_apply, CovarianceCorrector.fluctuation, Family.zero_apply]
      change (0 : ℝ) - average (fun _ => (0 : ℝ)) = 0
      rw [average_const, sub_self]
    · intro Z hZ hZS hz i p hp
      exact hz p hp
    · intro r hr hn
      omega
    · intro i
      exact MetricPolynomial.represents_initial hO hQ g hV hVg
  | succ n ih =>
    obtain ⟨U, hinit, hU, hy₁, hsupport, hcoeff, hrep⟩ := ih
    have hRs := MetricPolynomial.coefficients_smooth hO hY hC hX hV hd hq hqp hcircle dxIndex v n
    obtain ⟨W, hlow, hW, hxx, hxy, hyy, hzero, hWrep⟩ := polynomial_advance hO v g
      hY hC hX hV hd hq hqp hcircle hG hQ hYg hCg hXg hVg hqg
      dxIndex U (MetricPolynomial.coefficients Y C X₀ V q dxIndex v n) (n + 1) (by omega) hU hRs hrep
    refine ⟨W, (hlow 0 (by omega)).trans hinit, hW, ?_, ?_, ?_, ?_⟩
    · rw [g.yyCoefficient_congr (U := W) (W := U) (by omega : 0 < 1)
        (fun i hi => hlow i (by omega))]
      exact hy₁
    · intro Z hZ hZS hz
      exact hzero Z hZ hZS (hsupport Z hZ hZS hz)
    · intro r hr hn
      by_cases heq : r = n + 1
      · subst r
        exact ⟨hxx, hxy, hyy⟩
      · have hrn : r ≤ n := by omega
        obtain ⟨hx, hxy', hy⟩ := hcoeff r hr hrn
        rw [g.xxCoefficient_congr (fun i hi => hlow i (by omega)),
          g.xyCoefficient_congr (fun i hi => hlow i (by omega)),
          g.yyCoefficient_congr (by omega) (fun i hi => hlow i (by omega))]
        exact ⟨hx, hxy', hy⟩
    · exact hWrep

end ClosedSurfaceR4.JetPolynomial

end

end OAI
