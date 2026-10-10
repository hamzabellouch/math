import OAI.Geometry.SurfaceImmersion.Primitive.PeriodicAnsatzMetric
import OAI.Geometry.SurfaceImmersion.Primitive.PeriodicMetricRemainder

namespace OAI

/-! Exact finite metric expansion of the actual oscillatory map. -/

noncomputable section
open scoped BigOperators ContDiff

namespace ClosedSurfaceR4.PeriodicExpansion

open CovarianceCorrector

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

namespace Geometry

variable {dy : A} (g : Geometry (E := E) dy)

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma polynomial_zero_coefficients (dx : A) (U : ℕ → Family A E) (L : ℕ)
    (p : A) (t : Period) :
    (g.xxRemainder dx U L 0).val p t = inner ℝ (g.X₀ p) (g.X₀ p) + g.q p ∧
    (g.xyRemainder dx U L 0).val p t = inner ℝ (g.X₀ p) (g.Y p) ∧
    (g.yyRemainder U L 0).val p t = inner ℝ (g.Y p) (g.Y p) := by
  have hp := g.perpX₀ p _ (g.V_mem p t)
  have hy := g.perpY p _ (g.V_mem p t)
  have hp' : inner ℝ (g.V.val p t) (g.X₀ p) = 0 := by
    rw [real_inner_comm]
    exact hp
  have hy' : inner ℝ (g.V.val p t) (g.Y p) = 0 := by
    rw [real_inner_comm]
    exact hy
  simp only [xxRemainder, xyRemainder, yyRemainder, metricCoefficientFamily_apply,
    metricPolynomial_coeff (Nat.zero_le L), Finset.sum_range_one, Nat.sub_zero,
    xTangent_zero, yTangent_zero, longitudinal, transverse, Family.add_apply,
    Family.constant_apply, inner_add_left, inner_add_right, hp, hp', hy', g.circle p t, add_zero,
    zero_add]
  trivial

omit [FiniteDimensional ℝ E] in
/-- The exact metric identity, before replacing low coefficients by their means. -/
theorem finite_metric_identity {F : A → E} (hF : ContDiff ℝ ∞ F)
    (U : ℕ → Family A E) (hinit : U 0 = g.initial)
    (ℓ : A →L[ℝ] ℝ) (dx : A) (hℓx : ℓ dx = 1) (hℓy : ℓ dy = 0)
    (hX : ∀ p, fderiv ℝ F p dx = g.X₀ p + average (g.V.val p))
    (hY : ∀ p, fderiv ℝ F p dy = g.Y p)
    (n : ℕ) (z : ℝ) (hz : z ≠ 0) (p : A) :
    let f := finiteAnsatz F U ℓ (n + 1) z
    let t : Period := ((ℓ p / z : ℝ) : Period)
    let L := n + 1
    inner ℝ (fderiv ℝ f p dx) (fderiv ℝ f p dx) =
      (∑ r ∈ Finset.range L, (g.xxRemainder dx U L r).val p t * z ^ r) +
        ∑ r ∈ Finset.Ico L (2 * L + 1), (g.xxRemainder dx U L r).val p t * z ^ r ∧
    inner ℝ (fderiv ℝ f p dx) (fderiv ℝ f p dy) =
      (∑ r ∈ Finset.range L, (g.xyRemainder dx U L r).val p t * z ^ r) +
        ∑ r ∈ Finset.Ico L (2 * L + 1), (g.xyRemainder dx U L r).val p t * z ^ r ∧
    inner ℝ (fderiv ℝ f p dy) (fderiv ℝ f p dy) =
      (∑ r ∈ Finset.range L, (g.yyRemainder U L r).val p t * z ^ r) +
        ∑ r ∈ Finset.Ico L (2 * L + 1), (g.yyRemainder U L r).val p t * z ^ r := by
  dsimp only
  rw [g.finiteAnsatz_x hF U hinit ℓ dx hℓx hX n z hz p,
    g.finiteAnsatz_y hF U ℓ hℓy hY (n + 1) z p]
  simp only [xxRemainder, xyRemainder, yyRemainder, metricCoefficientFamily_apply]
  exact ⟨metricPolynomial_expansion (n + 1) (n + 1) (by omega) _ _ z,
    metricPolynomial_expansion (n + 1) (n + 1) (by omega) _ _ z,
    metricPolynomial_expansion (n + 1) (n + 1) (by omega) _ _ z⟩

end Geometry
end ClosedSurfaceR4.PeriodicExpansion

end

end OAI
