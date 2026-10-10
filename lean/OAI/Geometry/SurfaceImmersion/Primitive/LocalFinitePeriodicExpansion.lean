import OAI.Geometry.SurfaceImmersion.Primitive.LocalPeriodicFiniteMetricIdentity

namespace OAI

/-! Exact finite periodic expansion with angle-independent lower metric terms. -/

noncomputable section
open scoped BigOperators ContDiff

namespace ClosedSurfaceR4.LocalPeriodicExpansion

open CovarianceCorrector
open ClosedSurfaceR4.PeriodicExpansion (metricPolynomial metricPolynomial_coeff_pos
  metricPolynomial_coeff metricPolynomial_expansion vectorPolynomialValue
  weighted_sum_split_endpoints weighted_sum_split_zero shifted_derivative_sum)


private lemma replace_low_sum (n : ℕ) (c e : ℕ → ℝ) (q z : ℝ)
    (hzero : c 0 = q) (h : ∀ r, 0 < r → r < n + 1 → c r = e r) :
    (∑ r ∈ Finset.range (n + 1), c r * z ^ r) =
      q + ∑ r ∈ Finset.Ico 1 (n + 1), e r * z ^ r := by
  have hs := weighted_sum_split_zero z c n
  simp only [smul_eq_mul, mul_comm] at hs
  rw [hs, hzero]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  obtain ⟨hr, hrn⟩ := Finset.mem_Ico.mp hr
  rw [h r (by omega) hrn]

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  {O : TopologicalSpace.Opens A}

namespace Geometry

variable {dy : A} (g : Geometry (E := E) O dy)

/-- The exact finite expansion of the actual pullback metric. This asserts
smooth periodic coefficients and removes every low-order oscillation;
it does not yet assert the higher-jet order and uniform remainder bounds. -/
theorem finite_periodic_expansion {F : A → E} (hF : ContDiffOn ℝ ∞ F O)
    (ℓ : A →L[ℝ] ℝ) (dx : A) (hℓx : ℓ dx = 1) (hℓy : ℓ dy = 0)
    (hX : ∀ p ∈ O, fderiv ℝ F p dx = g.X₀ p + average (g.V.val p))
    (hY : ∀ p ∈ O, fderiv ℝ F p dy = g.Y p) (n : ℕ) :
    ∃ U : ℕ → Family O E,
      U 0 = g.initial ∧ (∀ i p, p ∈ O → average ((U i).val p) = 0) ∧
      (∀ Z : Set A, IsOpen Z → Z ⊆ O → (∀ p ∈ Z, g.initial.val p = 0) →
        ∀ i p, p ∈ Z → (U i).val p = 0) ∧
      ∀ z : ℝ, z ≠ 0 → ∀ p ∈ O,
      let L := n + 1
      let f := finiteAnsatz F U ℓ L z
      let t : Period := ((ℓ p / z : ℝ) : Period)
      inner ℝ (fderiv ℝ f p dx) (fderiv ℝ f p dx) =
        (inner ℝ (g.X₀ p) (g.X₀ p) + g.q p) +
        (∑ r ∈ Finset.Ico 1 L, average ((g.xxCoefficient dx U r).val p) * z ^ r) +
        (∑ r ∈ Finset.Ico L (2 * L + 1), (g.xxRemainder dx U L r).val p t * z ^ r) ∧
      inner ℝ (fderiv ℝ f p dx) (fderiv ℝ f p dy) =
        inner ℝ (g.X₀ p) (g.Y p) +
        (∑ r ∈ Finset.Ico 1 L, average ((g.xyCoefficient dx U r).val p) * z ^ r) +
        (∑ r ∈ Finset.Ico L (2 * L + 1), (g.xyRemainder dx U L r).val p t * z ^ r) ∧
      inner ℝ (fderiv ℝ f p dy) (fderiv ℝ f p dy) =
        inner ℝ (g.Y p) (g.Y p) +
        (∑ r ∈ Finset.Ico 1 L, average ((g.yyCoefficient U r).val p) * z ^ r) +
        (∑ r ∈ Finset.Ico L (2 * L + 1), (g.yyRemainder U L r).val p t * z ^ r) := by
  obtain ⟨U, hinit, hU, hsupport, hcoeff⟩ := g.exists_angle_independent_coefficients dx (n + 1)
  refine ⟨U, hinit, hU, hsupport, ?_⟩
  intro z hz p hpO
  dsimp only
  let t : Period := ((ℓ p / z : ℝ) : Period)
  obtain ⟨hxx, hxy, hyy⟩ := g.finite_metric_identity hF U hinit ℓ dx hℓx hℓy hX hY n z hz hpO
  obtain ⟨hxx₀, hxy₀, hyy₀⟩ := g.polynomial_zero_coefficients dx U (n + 1) hpO t
  rw [replace_low_sum n _ _ _ z hxx₀ (fun r hr hn => (hcoeff r hr hn p t).1)] at hxx
  rw [replace_low_sum n _ _ _ z hxy₀ (fun r hr hn => (hcoeff r hr hn p t).2.1)] at hxy
  rw [replace_low_sum n _ _ _ z hyy₀ (fun r hr hn => (hcoeff r hr hn p t).2.2)] at hyy
  exact ⟨hxx, hxy, hyy⟩

end Geometry
end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
