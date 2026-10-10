import OAI.Geometry.CylinderCovering.Convexity.GlobalDefinitions

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace

namespace CylinderCovering

abbrev Euclidean (d : ℕ) := EuclideanSpace ℝ (Fin d)

def simplexCarrier {d : ℕ} (v : Fin (d + 1) → Euclidean d) : Set (Euclidean d) :=
  convexHull ℝ (range v)

def orthogonalProjection {d : ℕ} (u x : Euclidean d) : Euclidean d :=
  x - inner ℝ u x • u

def simplexShadowArea {d : ℕ} (v : Fin (d + 1) → Euclidean d)
    (u : Euclidean d) : ℝ :=
  (Measure.euclideanHausdorffMeasure (d - 1)
    (orthogonalProjection u '' simplexCarrier v)).toReal

def longestChord {d : ℕ} (S : Set (Euclidean d)) (u : Euclidean d) : ℝ :=
  sSup {r : ℝ | 0 ≤ r ∧ ∃ x ∈ S, x + r • u ∈ S}

def simplexMinimumShadowArea {d : ℕ} (v : Fin (d + 1) → Euclidean d) : ℝ :=
  sInf {a : ℝ | ∃ u : Euclidean d, ‖u‖ = 1 ∧ a = simplexShadowArea v u}

def SimplexChordProjectionStatement : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ v : Fin (d + 1) → Euclidean d,
    AffineIndependent ℝ v →
    (∀ u : Euclidean d, ‖u‖ = 1 →
      0 < longestChord (simplexCarrier v) u ∧
      (∃ x ∈ simplexCarrier v,
        x + longestChord (simplexCarrier v) u • u ∈ simplexCarrier v) ∧
      simplexShadowArea v u * longestChord (simplexCarrier v) u =
        (d : ℝ) * volume.real (simplexCarrier v)) ∧
    (∃ u : Euclidean d, ‖u‖ = 1 ∧
      simplexShadowArea v u = simplexMinimumShadowArea v) ∧
    simplexMinimumShadowArea v =
      (d : ℝ) * volume.real (simplexCarrier v) / Metric.diam (simplexCarrier v)

def TetrahedronEdgeMinimizerStatement : Prop :=
  ∀ v : Fin 4 → Space, AffineIndependent ℝ v →
    ∃ i j : Fin 4, i ≠ j ∧
      shadowArea (convexHull ℝ (range v))
        (‖v j - v i‖⁻¹ • (v j - v i)) =
      minimumShadowArea (convexHull ℝ (range v))

def RegularProjectionNormalizationStatement : Prop :=
  ∀ v : Fin 4 → Space, AffineIndependent ℝ v →
    ∀ edge : ℝ, 0 < edge →
      (∀ i j : Fin 4, i ≠ j → dist (v i) (v j) = edge) →
      minimumShadowArea (convexHull ℝ (range v)) = edge ^ 2 / (2 * Real.sqrt 2) ∧
      ∀ i j : Fin 4, i ≠ j →
        shadowArea (convexHull ℝ (range v))
          (‖v j - v i‖⁻¹ • (v j - v i)) = edge ^ 2 / (2 * Real.sqrt 2)

def SimplexProjectionIdentityStatement : Prop :=
  SimplexChordProjectionStatement ∧ TetrahedronEdgeMinimizerStatement ∧
    RegularProjectionNormalizationStatement

end CylinderCovering

end

end OAI
