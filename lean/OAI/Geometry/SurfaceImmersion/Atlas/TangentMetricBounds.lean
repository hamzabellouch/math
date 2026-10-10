import OAI.Geometry.SurfaceImmersion.Correction.PolynomialMetricBounds

namespace OAI

/-! Apply the finite-tail estimate to the actual two tangent expansions. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.MetricPolynomial
open LocalPeriodicExpansion WeightedEstimates

def tangentExpression (X Y : VectorExpression) (R : ℕ → VectorExpression)
    (dx dy : Fin 2) (L : ℕ) (b : Bool) : ℕ → VectorExpression :=
  if b then xTangent X dx R L else yTangent Y dy R

def tangentFamily {S : TopologicalSpace.Opens Base} {dy : Base}
    (g : Geometry (E := R4) S dy) (U : ℕ → Family S R4) (dx : Base) (L : ℕ)
    (b : Bool) : ℕ → Family S R4 :=
  if b then g.xTangent dx U L else g.yTangent U

lemma smooth_tangentExpression {O : Set LowJet} (hO : IsOpen O)
    {X Y : VectorExpression} {R : ℕ → VectorExpression}
    (hX : X.SmoothCoeffs O) (hY : Y.SmoothCoeffs O) (hR : ∀ i, (R i).SmoothCoeffs O)
    (dx dy : Fin 2) (L : ℕ) (b : Bool) (i : ℕ) :
    (tangentExpression X Y R dx dy L b i).SmoothCoeffs O := by
  cases b
  · exact smooth_yTangent hO hY hR dy i
  · exact smooth_xTangent hO hX hR dx L i

lemma order_tangentExpression {X Y : VectorExpression} {R : ℕ → VectorExpression} {L : ℕ}
    (hL : 1 ≤ L) (hX : ∀ a, (X a).order ≤ 2) (hY : ∀ a, (Y a).order ≤ 2)
    (hR : ∀ j < L, ∀ a, (R j a).order ≤ 2 * j + 2)
    (dx dy : Fin 2) (b : Bool) {i : ℕ} (hi : i ≤ L) (a : Fin 4) :
    (tangentExpression X Y R dx dy L b i a).order ≤ 2 * L + 1 := by
  cases b
  · exact order_yTangent hL hY hR dy hi a
  · exact order_xTangent hL hX hR dx hi a

lemma represents_tangentExpression {S : TopologicalSpace.Opens Base} {O : Set LowJet}
    (hO : IsOpen O) {G : Base → Space} (hG : ContDiff ℝ ∞ G)
    (hQ : Set.MapsTo (lowJet G) S O) (dx dy : Fin 2)
    (g : Geometry (E := R4) S (coordinateVector dy))
    {X Y : VectorExpression} {R : ℕ → VectorExpression} {U : ℕ → Family S R4}
    (hX : VectorExpression.Represents G X g.longitudinal)
    (hY : VectorExpression.Represents G Y g.transverse)
    (hRs : ∀ i, (R i).SmoothCoeffs O) (hR : ∀ i, VectorExpression.Represents G (R i) (U i))
    (L : ℕ) (b : Bool) (i : ℕ) :
    VectorExpression.Represents G (tangentExpression X Y R dx dy L b i)
      (tangentFamily g U (coordinateVector dx) L b i) := by
  cases b
  · exact represents_yTangent hO hG hQ dy g hY hRs hR i
  · exact represents_xTangent hO hG hQ g hX hRs hR dx L i

/-- The two choices of tangent yield the xx, xy, and yy metric tails.
The exponent is fixed by the finite expression, independently of `m`. -/
theorem compact_tangent_metric_tail {S : TopologicalSpace.Opens Base} {O K : Set LowJet}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (X Y : VectorExpression) (R : ℕ → VectorExpression)
    (hXs : X.SmoothCoeffs O) (hYs : Y.SmoothCoeffs O) (hRs : ∀ i, (R i).SmoothCoeffs O)
    (L : ℕ) (hL : 1 ≤ L) (hX : ∀ a, (X a).order ≤ 2) (hY : ∀ a, (Y a).order ≤ 2)
    (hR : ∀ j < L, ∀ a, (R j a).order ≤ 2 * j + 2)
    (dx dy : Fin 2) (b c : Bool) (ℓ : Base →L[ℝ] ℝ) :
    ∃ d : ℕ, ∀ (m : ℕ) (B : ℝ), 1 ≤ B → ∃ D : ℝ, 0 ≤ D ∧
      ∀ (G : Base → Space) (s z : ℝ), 0 < z → z ≤ s → s ≤ 1 →
      ContDiff ℝ ∞ G → Set.MapsTo (lowJet G) S K →
      WeightedBound S s (m + (2 * L + 1)) B (lowJet G) →
      ∀ (g : Geometry (E := R4) S (coordinateVector dy)) (U : ℕ → Family S R4),
        VectorExpression.Represents G X g.longitudinal →
        VectorExpression.Represents G Y g.transverse →
        (∀ i, VectorExpression.Represents G (R i) (U i)) →
        WeightedBound S z m (D * z ^ L / s ^ d)
          (fun p => ∑ r ∈ Finset.Ico L (2 * L + 1), z ^ r *
            (metricCoefficientFamily L r (tangentFamily g U (coordinateVector dx) L b)
              (tangentFamily g U (coordinateVector dx) L c)).fastValue ℓ z p) := by
  obtain ⟨d, hd⟩ := compact_finite_metric_tail (S := S) hO hK hKO
    (tangentExpression X Y R dx dy L b) (tangentExpression X Y R dx dy L c)
    (smooth_tangentExpression hO hXs hYs hRs dx dy L b)
    (smooth_tangentExpression hO hXs hYs hRs dx dy L c) L (2 * L + 1) (by omega)
    (fun i hi a => order_tangentExpression hL hX hY hR dx dy b hi a)
    (fun i hi a => order_tangentExpression hL hX hY hR dx dy c hi a) ℓ
  refine ⟨d, ?_⟩
  intro m B hB
  obtain ⟨D, hD, hb⟩ := hd m B hB
  refine ⟨D, hD, ?_⟩
  intro G s z hz hzs hs1 hG hGK hGb g U hXg hYg hrep
  have hQ : Set.MapsTo (lowJet G) S O := fun _ hp => hKO (hGK hp)
  exact hb G s z hz hzs hs1 hG hGK hGb _ _
    (represents_tangentExpression hO hG hQ dx dy g hXg hYg hRs hrep L b)
    (represents_tangentExpression hO hG hQ dx dy g hXg hYg hRs hrep L c)

end ClosedSurfaceR4.JetPolynomial.MetricPolynomial

end

end OAI
