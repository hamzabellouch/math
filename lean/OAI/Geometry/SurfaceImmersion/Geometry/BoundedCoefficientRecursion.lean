import OAI.Geometry.SurfaceImmersion.Correction.PolynomialCoefficientRecursion
import OAI.Geometry.SurfaceImmersion.Geometry.FiniteFastBounds

namespace OAI

/-! The actual supported metric-cancelling recursion with uniform fast-scale
estimates. All losses are determined by the finite symbolic recursion before
the slow map or its scales are chosen. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open LocalPeriodicExpansion CovarianceCorrector WeightedEstimates

namespace VectorExpression

def finiteLoss (R : ℕ → VectorExpression) (L : ℕ) : ℕ :=
  (Finset.range L).sup (fun i => Finset.univ.sup (fun a => (R i a).loss))

lemma loss_le_finiteLoss (R : ℕ → VectorExpression) {i L : ℕ} (hi : i < L) (a : Fin 4) :
    (R i a).loss ≤ finiteLoss R L :=
  (Finset.le_sup (f := fun a => (R i a).loss) (Finset.mem_univ a)).trans
    (Finset.le_sup (f := fun i => Finset.univ.sup (fun a => (R i a).loss)) (Finset.mem_range.mpr hi))

end VectorExpression

/-- The support and cancellation identities belong to the very same finite
family whose oscillatory ansatz satisfies the quantitative estimate. -/
theorem exists_bounded_coefficients {S : TopologicalSpace.Opens Base} {O K : Set LowJet}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (dx dy : Fin 2) (n : ℕ) (ℓ : Base →L[ℝ] ℝ)
    {Y C X₀ : LowJet → R4} {V : LowJet → C(Period, R4)} {q : LowJet → ℝ}
    (hY : ContDiffOn ℝ ∞ Y O) (hC : ContDiffOn ℝ ∞ C O) (hX : ContDiffOn ℝ ∞ X₀ O)
    (hV : ContDiffOn ℝ ∞ (fun z : LowJet × ℝ => V z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (hdet : ∀ Q ∈ O, PeriodicCorrector.gramDet (Y Q) (C Q) ≠ 0)
    (hq : ContDiffOn ℝ ∞ q O) (hqp : ∀ Q ∈ O, 0 < q Q)
    (hcircle : ∀ Q ∈ O, ∀ t, inner ℝ (V Q t) (V Q t) = q Q) :
    ∃ d : ℕ, ∀ (m : ℕ) (B : ℝ), 1 ≤ B → ∃ D : ℝ, 0 ≤ D ∧
      ∀ (G : Base → Space) (g : Geometry (E := R4) S (coordinateVector dy)),
      ContDiff ℝ ∞ G → Set.MapsTo (lowJet G) S K →
      (∀ p ∈ S, g.Y p = Y (lowJet G p)) →
      (∀ p ∈ S, g.C p = C (lowJet G p)) →
      (∀ p ∈ S, g.X₀ p = X₀ (lowJet G p)) →
      (∀ p ∈ S, g.V.val p = V (lowJet G p)) →
      (∀ p ∈ S, g.q p = q (lowJet G p)) →
      ∃ U : ℕ → Family S R4,
        U 0 = g.initial ∧ (∀ i p, p ∈ S → average ((U i).val p) = 0) ∧
        (g.yyCoefficient U 1).fluct = 0 ∧
        (∀ Z : Set Base, IsOpen Z → Z ⊆ S → (∀ p ∈ Z, g.initial.val p = 0) →
          ∀ i p, p ∈ Z → (U i).val p = 0) ∧
        (∀ r, 1 ≤ r → r ≤ n →
          (g.xxCoefficient (coordinateVector dx) U r).fluct = 0 ∧
          (g.xyCoefficient (coordinateVector dx) U r).fluct = 0 ∧
          (g.yyCoefficient U (r + 1)).fluct = 0) ∧
        (∀ i, VectorExpression.Represents G
          (MetricPolynomial.coefficients Y C X₀ V q dx dy n i) (U i)) ∧
        ∀ (s z : ℝ), 0 < z → z ≤ s → s ≤ 1 →
          WeightedBound S s (m + (2 * n + 2)) B (lowJet G) → ∀ F : Base → R4,
          WeightedBound S z m (D * z / s ^ d)
            (fun p => finiteAnsatz F U ℓ (n + 1) z p - F p) := by
  let R := MetricPolynomial.coefficients Y C X₀ V q dx dy n
  let d := VectorExpression.finiteLoss R (n + 1)
  have hRs : ∀ i, (R i).SmoothCoeffs O :=
    MetricPolynomial.coefficients_smooth hO hY hC hX hV hdet hq hqp hcircle dx dy n
  refine ⟨d, ?_⟩
  intro m B hB
  obtain ⟨D, hD, hbound⟩ := VectorExpression.compact_finite_ansatz_bound (S := S)
    hO hK hKO R (n + 1) (2 * n + 2) d (fun i _ => hRs i)
    (fun i hi a => (MetricPolynomial.coefficients_order Y C X₀ V q dx dy n i a).trans (by omega))
    (fun i hi a => VectorExpression.loss_le_finiteLoss R hi a) ℓ m B hB
  refine ⟨D, hD, ?_⟩
  intro G g hG hGK hYg hCg hXg hVg hqg
  have hQ : Set.MapsTo (lowJet G) S O := fun _ hp => hKO (hGK hp)
  obtain ⟨U, hinit, hmean, hy, hsupport, hcancel, hrep⟩ :=
    exists_polynomial_coefficients hO dy g hY hC hX hV hdet hq hqp hcircle
      hG hQ hYg hCg hXg hVg hqg dx n
  refine ⟨U, hinit, hmean, hy, hsupport, hcancel, hrep, ?_⟩
  intro s z hz hzs hs1 hb F
  exact hbound G s z hz hzs hs1 hG hGK hb F U (fun i _ => hrep i)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
