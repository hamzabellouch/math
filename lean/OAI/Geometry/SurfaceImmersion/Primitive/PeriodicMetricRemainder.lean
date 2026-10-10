import OAI.Geometry.SurfaceImmersion.Correction.PeriodicPolynomialExpansion

namespace OAI

/-! Smooth coefficient families and exact remainder of the finite metric expansion. -/

noncomputable section
open scoped BigOperators

namespace ClosedSurfaceR4.PeriodicExpansion

open CovarianceCorrector

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

def metricCoefficientFamily (n r : ℕ) (a b : ℕ → Family A E) : Family A ℝ :=
  ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
    if i + j = r then (a i).inner (b j) else 0

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma metricCoefficientFamily_apply (n r : ℕ) (a b : ℕ → Family A E) (p : A) (t : Period) :
    (metricCoefficientFamily n r a b).val p t =
      (metricPolynomial n (fun i => (a i).val p t) (fun i => (b i).val p t)).coeff r := by
  simp only [metricCoefficientFamily, Family.sum_apply, metricPolynomial, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs with h
  · simp only [h, Family.inner_apply, Polynomial.coeff_monomial_same]
  · simp only [Polynomial.coeff_monomial, h, ite_false, Family.zero_apply]

namespace Geometry

variable {dy : A} (g : Geometry (E := E) dy)

def xxRemainder (dx : A) (U : ℕ → Family A E) (L r : ℕ) : Family A ℝ :=
  metricCoefficientFamily L r (g.xTangent dx U L) (g.xTangent dx U L)

def xyRemainder (dx : A) (U : ℕ → Family A E) (L r : ℕ) : Family A ℝ :=
  metricCoefficientFamily L r (g.xTangent dx U L) (g.yTangent U)

def yyRemainder (U : ℕ → Family A E) (L r : ℕ) : Family A ℝ :=
  metricCoefficientFamily L r (g.yTangent U) (g.yTangent U)

/-- Every finite construction has jointly smooth remainder coefficients.
The prescribed lower coefficients are independent of the fast angle. -/
theorem exists_angle_independent_coefficients (dx : A) (L : ℕ) :
    ∃ U : ℕ → Family A E,
      U 0 = g.initial ∧ (∀ i p, average ((U i).val p) = 0) ∧
      (∀ O : Set A, IsOpen O → (∀ p ∈ O, g.initial.val p = 0) →
        ∀ i p, p ∈ O → (U i).val p = 0) ∧
      ∀ r, 0 < r → r < L → ∀ p t,
        (g.xxRemainder dx U L r).val p t = average ((g.xxCoefficient dx U r).val p) ∧
        (g.xyRemainder dx U L r).val p t = average ((g.xyCoefficient dx U r).val p) ∧
        (g.yyRemainder U L r).val p t = average ((g.yyCoefficient U r).val p) := by
  obtain ⟨U, hinit, hU, hy₁, hsupport, hcoeff⟩ := g.exists_coefficients dx L
  refine ⟨U, hinit, hU, hsupport, ?_⟩
  intro r hr hL p t
  obtain ⟨hx, hxy, _⟩ := hcoeff r hr (by omega)
  have hy : (g.yyCoefficient U r).fluct = 0 := by
    by_cases he : r = 1
    · simpa only [he] using hy₁
    · have hprev := (hcoeff (r - 1) (by omega) (by omega)).2.2
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ r)] using hprev
  have mean_eq (f : Family A ℝ) (hf : f.fluct = 0) : f.val p t = average (f.val p) := by
    have ht := congrArg (fun w : Family A ℝ => w.val p t) hf
    change f.val p t - average (f.val p) = 0 at ht
    exact sub_eq_zero.mp ht
  change (metricCoefficientFamily L r _ _).val p t = _ ∧
    (metricCoefficientFamily L r _ _).val p t = _ ∧
    (metricCoefficientFamily L r _ _).val p t = _
  simp only [metricCoefficientFamily_apply]
  exact ⟨(g.xxPolynomial_coeff dx U hr hL p t).trans (mean_eq _ hx),
    (g.xyPolynomial_coeff dx U hr hL p t).trans (mean_eq _ hxy),
    (g.yyPolynomial_coeff U hr (by omega) p t).trans (mean_eq _ hy)⟩

end Geometry
end ClosedSurfaceR4.PeriodicExpansion

end

end OAI
