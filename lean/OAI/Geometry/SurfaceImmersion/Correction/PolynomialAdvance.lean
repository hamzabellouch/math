import OAI.Geometry.SurfaceImmersion.Correction.PolynomialForcingRepresentation
import OAI.Geometry.SurfaceImmersion.Primitive.LocalPeriodicTriangularRecursion

namespace OAI

/-! The actual triangular correction step, retaining its polynomial representation. -/
noncomputable section
open scoped ContDiff Topology
namespace ClosedSurfaceR4.JetPolynomial
open CovarianceCorrector LocalPeriodicExpansion

theorem polynomial_advance {S : TopologicalSpace.Opens Base} {O : Set LowJet}
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
    (dxIndex : Fin 2) (U : ℕ → Family S R4) (R : ℕ → VectorExpression) (r : ℕ) (hr : 0 < r)
    (hU : ∀ i p, p ∈ S → average ((U i).val p) = 0)
    (hRs : ∀ i, (R i).SmoothCoeffs O)
    (hR : ∀ i, VectorExpression.Represents G (R i) (U i)) :
    ∃ W : ℕ → Family S R4,
      (∀ i < r, W i = U i) ∧ (∀ i p, p ∈ S → average ((W i).val p) = 0) ∧
      (g.xxCoefficient (coordinateVector dxIndex) W r).fluct = 0 ∧
      (g.xyCoefficient (coordinateVector dxIndex) W r).fluct = 0 ∧
      (g.yyCoefficient W (r + 1)).fluct = 0 ∧
      (∀ Z : Set Base, IsOpen Z → Z ⊆ S → (∀ i p, p ∈ Z → (U i).val p = 0) →
        ∀ i p, p ∈ Z → (W i).val p = 0) ∧
      (∀ i, VectorExpression.Represents G
        (Function.update R r (MetricPolynomial.step Y C X₀ V q dxIndex v R r) i) (W i)) := by
  let dx : Base := coordinateVector dxIndex
  let dy : Base := coordinateVector v
  let b := g.longitudinal.inner (yCoefficient dy U r) +
    g.transverse.inner ((U (r - 1)).slow dx) + xyQuadratic dx dy U r
  let c := g.longitudinal.inner ((U (r - 1)).slow dx) +
    (1 / 2 : ℝ) • xxQuadratic dx U r
  let d := yyQuadratic dy U (r + 1)
  let pb := MetricPolynomial.mixedForcing (MetricPolynomial.longitudinal X₀ V)
    (MetricPolynomial.transverse Y) dxIndex v R r
  let pc := MetricPolynomial.longitudinalForcing (MetricPolynomial.longitudinal X₀ V) dxIndex R r
  let pd := MetricPolynomial.transverseForcing v R r
  have hlong := MetricPolynomial.represents_longitudinal g X₀ V hXg hVg
  have htrans := MetricPolynomial.represents_transverse g Y hYg
  have hpbr : Expression.Represents G pb b :=
    MetricPolynomial.represents_mixedForcing hO hG hQ hRs hR hlong htrans dxIndex v r
  have hpcr : Expression.Represents G pc c :=
    MetricPolynomial.represents_longitudinalForcing hO hG hQ hRs hR hlong dxIndex r
  have hpdr : Expression.Represents G pd d :=
    MetricPolynomial.represents_transverseForcing hO hG hQ hRs hR v r
  have hpbs : pb.SmoothCoeffs O := MetricPolynomial.smooth_mixedForcing hO hRs
    (MetricPolynomial.smooth_longitudinal hX hV) (MetricPolynomial.smooth_transverse hY) dxIndex v r
  have hpcs : pc.SmoothCoeffs O := MetricPolynomial.smooth_longitudinalForcing hO hRs
    (MetricPolynomial.smooth_longitudinal hX hV) dxIndex r
  have hpds : pd.SmoothCoeffs O := MetricPolynomial.smooth_yyQuadratic hO hRs v (r + 1)
  obtain ⟨u, hu0, hb, hc, hd', hzero, hurep⟩ := exists_polynomial_cancellation hO v g
    hY hC hX hV hd hq hqp hcircle hG hQ hYg hCg hXg hVg hqg
    hpbs hpcs hpds b c d hpbr hpcr hpdr
  let W := Function.update U r u
  have hlow (i : ℕ) (hi : i < r) : W i = U i := by
    exact Function.update_of_ne (a := i) (a' := r) (by omega) u U
  have hprev : W (r - 1) = U (r - 1) := hlow _ (by omega)
  have hcur : W r = u := Function.update_self r u U
  have hA : xCoefficient dx W r = (U (r - 1)).slow dx + u.angle := by
    simp only [xCoefficient, hprev, hcur]
  have hB : yCoefficient dy W r = yCoefficient dy U r := yCoefficient_congr hprev
  have hB' : yCoefficient dy W (r + 1) = u.slow dy := by
    simp only [yCoefficient, Nat.add_sub_cancel, hcur]
  have hxx := xxQuadratic_congr (dx := dx) hlow
  have hxy := xyQuadratic_congr (dx := dx) (dy := dy) hlow
  have hyy : yyQuadratic dy W (r + 1) = d :=
    yyQuadratic_congr (fun i hi => hlow i (by omega))
  refine ⟨W, hlow, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i p hp
    by_cases hi : i = r
    · subst i
      rw [hcur]
      exact hu0 p hp
    · rw [show W i = U i from Function.update_of_ne hi u U]
      exact hU i p hp
  · have he : g.xxCoefficient dx W r =
        (2 : ℝ) • (g.longitudinal.inner u.angle + c) := by
      unfold Geometry.xxCoefficient c
      rw [hA, hxx, Family.inner_add_right]
      module
    rw [he, Family.fluct_smul, hc, smul_zero]
  · have he : g.xyCoefficient dx W r = g.transverse.inner u.angle + b := by
      unfold Geometry.xyCoefficient b
      rw [hA, hB, hxy, Family.inner_add_right]
      abel
    rw [he, hb]
  · change ((2 : ℝ) • g.transverse.inner (yCoefficient dy W (r + 1)) +
      yyQuadratic dy W (r + 1)).fluct = 0
    rw [hB', hyy]
    exact hd'
  · intro Z hO hZO hUO i p hp
    have huO : ∀ q ∈ Z, u.val q = 0 := by
      apply hzero Z hO hZO
      · intro q hq
        ext t
        have hs := (U (r - 1)).slow_zero_on hO (hUO (r - 1)) dx (hZO hq) hq
        simp only [b, Family.add_apply, Family.inner_apply,
          yCoefficient_zero_on hO hZO U hUO dy r hq, hs,
          xyQuadratic_zero_on hO hZO U hUO dx dy r hq,
          ContinuousMap.zero_apply, inner_zero_right, add_zero]
      · intro q hq
        ext t
        have hs := (U (r - 1)).slow_zero_on hO (hUO (r - 1)) dx (hZO hq) hq
        simp only [c, Family.add_apply, Family.smul_apply, Family.inner_apply,
          hs, xxQuadratic_zero_on hO hZO U hUO dx r hq,
          ContinuousMap.zero_apply, inner_zero_right, smul_zero, add_zero]
      · intro q hq
        exact yyQuadratic_zero_on hO hZO U hUO dy (r + 1) hq
    by_cases hi : i = r
    · subst i
      rw [hcur]
      exact huO p hp
    · rw [show W i = U i from Function.update_of_ne hi u U]
      exact hUO i p hp

  · intro i
    by_cases hi : i = r
    · subst i
      rw [Function.update_self, hcur]
      exact hurep
    · rw [Function.update_of_ne hi, show W i = U i from Function.update_of_ne hi u U]
      exact hR i

end ClosedSurfaceR4.JetPolynomial

end

end OAI
