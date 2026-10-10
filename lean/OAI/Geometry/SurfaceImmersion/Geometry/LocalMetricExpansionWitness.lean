import OAI.Geometry.SurfaceImmersion.Primitive.LocalFinitePeriodicExpansion

namespace OAI

/-! The finite metric expansion for a specified cancelling coefficient
sequence, allowing the quantitative estimates to use the same witness. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.LocalPeriodicExpansion
open CovarianceCorrector
open ClosedSurfaceR4.PeriodicExpansion (weighted_sum_split_zero)

private lemma split_constant (n : ℕ) (c e : ℕ → ℝ) (q z : ℝ)
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
  [CompleteSpace E] {O : TopologicalSpace.Opens A} {dy : A}

namespace Geometry

omit [CompleteSpace E] in
lemma angle_independent_of_cancellation (g : Geometry (E := E) O dy)
    (dx : A) (U : ℕ → Family O E) (n : ℕ)
    (hy₁ : (g.yyCoefficient U 1).fluct = 0)
    (hc : ∀ r, 1 ≤ r → r ≤ n →
      (g.xxCoefficient dx U r).fluct = 0 ∧
      (g.xyCoefficient dx U r).fluct = 0 ∧ (g.yyCoefficient U (r + 1)).fluct = 0)
    {r : ℕ} (hr : 0 < r) (hrn : r < n + 1) (p : A) (t : Period) :
    (g.xxRemainder dx U (n + 1) r).val p t = average ((g.xxCoefficient dx U r).val p) ∧
    (g.xyRemainder dx U (n + 1) r).val p t = average ((g.xyCoefficient dx U r).val p) ∧
    (g.yyRemainder U (n + 1) r).val p t = average ((g.yyCoefficient U r).val p) := by
  obtain ⟨hx, hxy, _⟩ := hc r hr (by omega)
  have hy : (g.yyCoefficient U r).fluct = 0 := by
    by_cases he : r = 1
    · simpa only [he] using hy₁
    · simpa only [Nat.sub_add_cancel (by omega : 1 ≤ r)] using
        (hc (r - 1) (by omega) (by omega)).2.2
  have mean_eq (f : Family O ℝ) (hf : f.fluct = 0) : f.val p t = average (f.val p) := by
    have ht := congrArg (fun w : Family O ℝ => w.val p t) hf
    simp only [Family.fluct_apply, fluctuation, Family.zero_apply] at ht
    exact sub_eq_zero.mp ht
  change (metricCoefficientFamily (n + 1) r _ _).val p t = _ ∧
    (metricCoefficientFamily (n + 1) r _ _).val p t = _ ∧
    (metricCoefficientFamily (n + 1) r _ _).val p t = _
  simp only [metricCoefficientFamily_apply]
  exact ⟨(g.xxPolynomial_coeff dx U hr hrn p t).trans (mean_eq _ hx),
    (g.xyPolynomial_coeff dx U hr hrn p t).trans (mean_eq _ hxy),
    (g.yyPolynomial_coeff U hr (by omega) p t).trans (mean_eq _ hy)⟩

/-- The exact expansion retains a given coefficient witness, rather than
choosing a new sequence without its proved estimates. -/
theorem finite_expansion_of_cancellation (g : Geometry (E := E) O dy)
    {F : A → E} (hF : ContDiffOn ℝ ∞ F O) (U : ℕ → Family O E)
    (hinit : U 0 = g.initial) (n : ℕ) (dx : A)
    (hy₁ : (g.yyCoefficient U 1).fluct = 0)
    (hc : ∀ r, 1 ≤ r → r ≤ n →
      (g.xxCoefficient dx U r).fluct = 0 ∧
      (g.xyCoefficient dx U r).fluct = 0 ∧ (g.yyCoefficient U (r + 1)).fluct = 0)
    (ℓ : A →L[ℝ] ℝ) (hℓx : ℓ dx = 1) (hℓy : ℓ dy = 0)
    (hX : ∀ p ∈ O, fderiv ℝ F p dx = g.X₀ p + average (g.V.val p))
    (hY : ∀ p ∈ O, fderiv ℝ F p dy = g.Y p)
    (z : ℝ) (hz : z ≠ 0) {p : A} (hp : p ∈ O) :
    let f := finiteAnsatz F U ℓ (n + 1) z
    let t : Period := ((ℓ p / z : ℝ) : Period)
    inner ℝ (fderiv ℝ f p dx) (fderiv ℝ f p dx) =
      (inner ℝ (g.X₀ p) (g.X₀ p) + g.q p) +
      (∑ r ∈ Finset.Ico 1 (n + 1), average ((g.xxCoefficient dx U r).val p) * z ^ r) +
      (∑ r ∈ Finset.Ico (n + 1) (2 * (n + 1) + 1),
        (g.xxRemainder dx U (n + 1) r).val p t * z ^ r) ∧
    inner ℝ (fderiv ℝ f p dx) (fderiv ℝ f p dy) =
      inner ℝ (g.X₀ p) (g.Y p) +
      (∑ r ∈ Finset.Ico 1 (n + 1), average ((g.xyCoefficient dx U r).val p) * z ^ r) +
      (∑ r ∈ Finset.Ico (n + 1) (2 * (n + 1) + 1),
        (g.xyRemainder dx U (n + 1) r).val p t * z ^ r) ∧
    inner ℝ (fderiv ℝ f p dy) (fderiv ℝ f p dy) =
      inner ℝ (g.Y p) (g.Y p) +
      (∑ r ∈ Finset.Ico 1 (n + 1), average ((g.yyCoefficient U r).val p) * z ^ r) +
      (∑ r ∈ Finset.Ico (n + 1) (2 * (n + 1) + 1),
        (g.yyRemainder U (n + 1) r).val p t * z ^ r) := by
  dsimp only
  let t : Period := ((ℓ p / z : ℝ) : Period)
  obtain ⟨hxx, hxy, hyy⟩ := g.finite_metric_identity hF U hinit ℓ dx hℓx hℓy hX hY n z hz hp
  obtain ⟨hxx₀, hxy₀, hyy₀⟩ := g.polynomial_zero_coefficients dx U (n + 1) hp t
  have hcoeff := fun (r : ℕ) (hr : 0 < r) (hn : r < n + 1) =>
    g.angle_independent_of_cancellation dx U n hy₁ hc hr hn p t
  rw [split_constant n _ _ _ z hxx₀ (fun r hr hn => (hcoeff r hr hn).1)] at hxx
  rw [split_constant n _ _ _ z hxy₀ (fun r hr hn => (hcoeff r hr hn).2.1)] at hxy
  rw [split_constant n _ _ _ z hyy₀ (fun r hr hn => (hcoeff r hr hn).2.2)] at hyy
  exact ⟨hxx, hxy, hyy⟩

end Geometry
end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
