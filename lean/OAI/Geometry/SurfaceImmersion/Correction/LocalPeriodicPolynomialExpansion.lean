import OAI.Geometry.SurfaceImmersion.Primitive.LocalPeriodicTriangularRecursion
import OAI.Geometry.SurfaceImmersion.Correction.FiniteMetricPolynomial
import OAI.Geometry.SurfaceImmersion.Geometry.FiniteSeriesAlgebra

namespace OAI

/-! Metric polynomial coefficients of the finite periodic derivative ansatz. -/

noncomputable section
open scoped BigOperators

namespace ClosedSurfaceR4.LocalPeriodicExpansion

open CovarianceCorrector
open ClosedSurfaceR4.PeriodicExpansion (metricPolynomial metricPolynomial_coeff_pos
  metricPolynomial_coeff metricPolynomial_expansion vectorPolynomialValue
  weighted_sum_split_endpoints weighted_sum_split_zero shifted_derivative_sum)


variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  {O : TopologicalSpace.Opens A}

namespace Geometry

variable {dy : A} (g : Geometry (E := E) O dy)

def xTangent (dx : A) (U : ℕ → Family O E) (L i : ℕ) : Family O E :=
  if i = 0 then g.longitudinal else
  if i = L then (U (i - 1)).slow dx else xCoefficient dx U i

def yTangent (U : ℕ → Family O E) (i : ℕ) : Family O E :=
  if i = 0 then g.transverse else yCoefficient dy U i

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp] lemma xTangent_zero (dx : A) (U : ℕ → Family O E) (L : ℕ) :
    g.xTangent dx U L 0 = g.longitudinal := by simp [xTangent]

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp] lemma yTangent_zero (U : ℕ → Family O E) : g.yTangent U 0 = g.transverse := by
  simp [yTangent]

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma xTangent_interior (dx : A) (U : ℕ → Family O E) {L i : ℕ}
    (hi : 0 < i) (hL : i < L) : g.xTangent dx U L i = xCoefficient dx U i := by
  simp only [xTangent, ne_of_gt hi, ne_of_lt hL, ite_false]

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma yTangent_pos (U : ℕ → Family O E) {i : ℕ} (hi : 0 < i) :
    g.yTangent U i = yCoefficient dy U i := by
  simp only [yTangent, ne_of_gt hi, ite_false]

def xxPolynomial (dx : A) (U : ℕ → Family O E) (L : ℕ) (p : A) (t : Period) : Polynomial ℝ :=
  metricPolynomial L (fun i => (g.xTangent dx U L i).val p t)
    (fun i => (g.xTangent dx U L i).val p t)

def xyPolynomial (dx : A) (U : ℕ → Family O E) (L : ℕ) (p : A) (t : Period) : Polynomial ℝ :=
  metricPolynomial L (fun i => (g.xTangent dx U L i).val p t)
    (fun i => (g.yTangent U i).val p t)

def yyPolynomial (U : ℕ → Family O E) (L : ℕ) (p : A) (t : Period) : Polynomial ℝ :=
  metricPolynomial L (fun i => (g.yTangent U i).val p t)
    (fun i => (g.yTangent U i).val p t)

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma xxPolynomial_coeff (dx : A) (U : ℕ → Family O E) {L r : ℕ}
    (hr : 0 < r) (hL : r < L) (p : A) (t : Period) :
    (g.xxPolynomial dx U L p t).coeff r = (g.xxCoefficient dx U r).val p t := by
  unfold xxPolynomial
  rw [metricPolynomial_coeff_pos (Nat.le_of_lt hL) hr,
    g.xTangent_zero, g.xTangent_interior dx U hr hL]
  have hs : (∑ i ∈ Finset.Ico 1 r,
      inner ℝ ((g.xTangent dx U L i).val p t) ((g.xTangent dx U L (r - i)).val p t)) =
      (xxQuadratic dx U r).val p t := by
    simp only [xxQuadratic, Family.sum_apply, Family.inner_apply]
    apply Finset.sum_congr rfl
    intro i hi
    obtain ⟨hi, hir⟩ := Finset.mem_Ico.mp hi
    rw [g.xTangent_interior dx U (by omega) (by omega),
      g.xTangent_interior dx U (by omega) (by omega)]
  rw [hs]
  simp only [xxCoefficient, Family.add_apply, Family.smul_apply, Family.inner_apply, smul_eq_mul]
  rw [real_inner_comm ((xCoefficient dx U r).val p t) (g.longitudinal.val p t)]
  ring

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma xyPolynomial_coeff (dx : A) (U : ℕ → Family O E) {L r : ℕ}
    (hr : 0 < r) (hL : r < L) (p : A) (t : Period) :
    (g.xyPolynomial dx U L p t).coeff r = (g.xyCoefficient dx U r).val p t := by
  unfold xyPolynomial
  rw [metricPolynomial_coeff_pos (Nat.le_of_lt hL) hr,
    g.xTangent_zero, g.xTangent_interior dx U hr hL, g.yTangent_zero, g.yTangent_pos U hr]
  have hs : (∑ i ∈ Finset.Ico 1 r,
      inner ℝ ((g.xTangent dx U L i).val p t) ((g.yTangent U (r - i)).val p t)) =
      (xyQuadratic dx dy U r).val p t := by
    simp only [xyQuadratic, Family.sum_apply, Family.inner_apply]
    apply Finset.sum_congr rfl
    intro i hi
    obtain ⟨hi, hir⟩ := Finset.mem_Ico.mp hi
    rw [g.xTangent_interior dx U (by omega) (by omega), g.yTangent_pos U (by omega)]
  rw [hs]
  simp only [xyCoefficient, Family.add_apply, Family.inner_apply]
  rw [real_inner_comm ((xCoefficient dx U r).val p t) (g.transverse.val p t)]

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma yyPolynomial_coeff (U : ℕ → Family O E) {L r : ℕ}
    (hr : 0 < r) (hL : r ≤ L) (p : A) (t : Period) :
    (g.yyPolynomial U L p t).coeff r = (g.yyCoefficient U r).val p t := by
  unfold yyPolynomial
  rw [metricPolynomial_coeff_pos hL hr, g.yTangent_zero, g.yTangent_pos U hr]
  have hs : (∑ i ∈ Finset.Ico 1 r,
      inner ℝ ((g.yTangent U i).val p t) ((g.yTangent U (r - i)).val p t)) =
      (yyQuadratic dy U r).val p t := by
    simp only [yyQuadratic, Family.sum_apply, Family.inner_apply]
    apply Finset.sum_congr rfl
    intro i hi
    obtain ⟨hi, hir⟩ := Finset.mem_Ico.mp hi
    rw [g.yTangent_pos U (by omega), g.yTangent_pos U (by omega)]
  rw [hs]
  simp only [yyCoefficient, Family.add_apply, Family.smul_apply, Family.inner_apply, smul_eq_mul]
  rw [real_inner_comm ((yCoefficient dy U r).val p t) (g.transverse.val p t)]
  ring

end Geometry
end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
