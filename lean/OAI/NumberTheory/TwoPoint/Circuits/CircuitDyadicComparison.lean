import OAI.NumberTheory.TwoPoint.Circuits.CircuitDyadicApproximation
import OAI.NumberTheory.TwoPoint.Circuits.CircuitDyadicErrors
import OAI.NumberTheory.TwoPoint.Circuits.CircuitApproximationComparison

namespace OAI

/-! The fixed-depth bounded-independence theorem with a completely
explicit polynomial budget, stated first at dyadic accuracy. -/

namespace TwoPointCorrelations

open scoped Classical

theorem AC0Circuit.dyadic_comparison_lower {n j t : ℕ} (c : AC0Circuit n)
    (hc : c.depth ≤ 22) (hm : c.size ≤ 2 ^ j) (ht : bravermanDegree j ≤ t)
    (g : BooleanCube n → ℝ) (hg : ∀ x, 0 ≤ g x) (hmean : cubeAverage g = 1)
    (hwise : TWiseUniformDensity g t) :
    cubeAverage c.indicator - (1 / 2 : ℝ) ^ j ≤
      cubeAverage (fun x => g x * c.indicator x) := by
  obtain ⟨P, E, hP, hdepth, hsize, hprob, hexact, hnorm⟩ :=
    c.dyadic_approximation (mixedCubeLaw g hg hmean) hc hm
  let D := switchingDegree 89 (bravermanSwitches j)
  have herror : cubeAverage (fun x => (E.indicator x - walshTruncation E.indicator D x) ^ 2) ≤
      4 * (2 : ℝ) ^ bravermanErrorExponent j *
        (1 / 2 : ℝ) ^ (bravermanSwitches j + 1) := by
    apply (E.fourier_tail_polynomial_degree 89 (bravermanSwitches j) hdepth
      (bravermanSwitches_pos j)).trans
    have hreal : (E.size : ℝ) ≤ (2 : ℝ) ^ bravermanErrorExponent j := by
      exact_mod_cast hsize
    gcongr
  have hF (x) : c.indicator x = 0 ∨ c.indicator x = 1 := by
    cases he : c.eval x <;> simp [AC0Circuit.indicator, he]
  have hbound : 1 ≤ (2 : ℝ) ^ bravermanNormExponent j := one_le_pow₀ (by norm_num)
  have hdegree : (bravermanBase j ^ 22 + D) + (bravermanBase j ^ 22 + D) ≤ t := by
    dsimp [bravermanDegree] at ht
    dsimp [D]
    omega
  have hh := hwise.approximation_lower hg hmean hF hP
    (walshTruncation_degree E.indicator D) hdegree
    (fun x hx => hexact x (by simp [hx])) hbound hnorm hprob herror
  have hloss := braverman_total_loss j
  linarith

theorem AC0Circuit.dyadic_comparison {n j t : ℕ} (c : AC0Circuit n)
    (hc : c.depth ≤ 22) (hm : c.size ≤ 2 ^ j) (ht : bravermanDegree j ≤ t)
    (g : BooleanCube n → ℝ) (hg : ∀ x, 0 ≤ g x) (hmean : cubeAverage g = 1)
    (hwise : TWiseUniformDensity g t) :
    |cubeAverage (fun x => g x * c.indicator x) - cubeAverage c.indicator| ≤
      (1 / 2 : ℝ) ^ j := by
  have hlo := c.dyadic_comparison_lower hc hm ht g hg hmean hwise
  have hhi := c.negate.dyadic_comparison_lower (by simpa [AC0Circuit.negate_depth] using hc)
    (by simpa [AC0Circuit.negate_size] using hm) ht g hg hmean hwise
  have hu : cubeAverage c.negate.indicator = 1 - cubeAverage c.indicator := by
    change cubeAverage (fun x => c.negate.indicator x) = _
    simp_rw [AC0Circuit.negate_indicator]
    rw [cubeAverage_sub, cubeAverage_const]
  have hgneg : cubeAverage (fun x => g x * c.negate.indicator x) =
      1 - cubeAverage (fun x => g x * c.indicator x) := by
    simp_rw [AC0Circuit.negate_indicator, mul_sub, mul_one]
    rw [cubeAverage_sub, hmean]
  rw [hu, hgneg] at hhi
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end TwoPointCorrelations

end OAI
