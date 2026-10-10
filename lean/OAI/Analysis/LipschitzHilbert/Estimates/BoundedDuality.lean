import OAI.Analysis.LipschitzHilbert.Phase.ImprovedFourthMoment
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! Passing the interpolated simple-test pairing estimate to a bounded
canonical dual test. Only finite measures and bounded functions are needed. -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ComplexConjugate

namespace LipschitzHilbert.PhaseCombinatorics

theorem bounded_test_of_simple_tests (ν : Measure ℝ) [IsFiniteMeasure ν]
    (F : ℝ → ℂ) (hF : Measurable F) {A : ℝ} (hA : 0 ≤ A)
    (hFbound : ∀ x, ‖F x‖ ≤ A) {q : ℝ} (hq : 0 < q)
    (htest : ∀ g : SimpleFunc ℝ ℂ,
      ‖∫ x, F x * g x ∂ν‖ ≤ (∫ x, ‖g x‖ ^ q ∂ν) ^ (1 / q))
    (g : ℝ → ℂ) (hg : Measurable g) {B : ℝ}
    (hgbound : ∀ x, ‖g x‖ ≤ B) :
    ‖∫ x, F x * g x ∂ν‖ ≤ (∫ x, ‖g x‖ ^ q ∂ν) ^ (1 / q) := by
  let gₙ := fun n => SimpleFunc.approxOn g hg Set.univ 0 (Set.mem_univ _) n
  have happrox (x : ℝ) : Tendsto (fun n => gₙ n x) atTop (𝓝 (g x)) :=
    SimpleFunc.tendsto_approxOn hg (Set.mem_univ _) (by simp)
  have hbound (n : ℕ) (x : ℝ) : ‖gₙ n x‖ ≤ 2 * B := by
    have h := SimpleFunc.norm_approxOn_zero_le hg (Set.mem_univ (0 : ℂ)) x n
    exact h.trans (by nlinarith [hgbound x])
  have hpair : Tendsto (fun n => ∫ x, F x * gₙ n x ∂ν) atTop
      (𝓝 (∫ x, F x * g x ∂ν)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => A * (2 * B))
    · intro n
      exact (hF.mul (gₙ n).measurable).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      exact Filter.Eventually.of_forall fun x => by
        rw [norm_mul]
        exact mul_le_mul (hFbound x) (hbound n x) (norm_nonneg _) hA
    · exact Filter.Eventually.of_forall fun x => tendsto_const_nhds.mul (happrox x)
  have hpower : Tendsto (fun n => ∫ x, ‖gₙ n x‖ ^ q ∂ν) atTop
      (𝓝 (∫ x, ‖g x‖ ^ q ∂ν)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => (2 * B) ^ q)
    · intro n
      exact ((gₙ n).measurable.norm.pow_const q).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      exact Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
        exact Real.rpow_le_rpow (norm_nonneg _) (hbound n x) hq.le
    · exact Filter.Eventually.of_forall fun x =>
        ((Real.continuous_rpow_const hq.le).tendsto _).comp (happrox x).norm
  have hroot := ((Real.continuous_rpow_const (by positivity : 0 ≤ 1 / q)).tendsto _).comp hpower
  exact le_of_tendsto_of_tendsto' hpair.norm hroot (fun n => htest (gₙ n))

def canonicalDual (F : ℝ → ℂ) (p : ℝ) (x : ℝ) : ℂ :=
  conj (F x) * (‖F x‖ ^ (p - 2) : ℝ)

theorem canonicalDual_measurable {F : ℝ → ℂ} (hF : Measurable F) (p : ℝ) :
    Measurable (canonicalDual F p) := by
  exact (Complex.continuous_conj.measurable.comp hF).mul
    ((hF.norm.pow_const (p - 2)).complex_ofReal)

theorem canonicalDual_norm (F : ℝ → ℂ) {p : ℝ} (hp : 1 < p) (x : ℝ) :
    ‖canonicalDual F p x‖ = ‖F x‖ ^ (p - 1) := by
  unfold canonicalDual
  rw [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  by_cases hx : F x = 0
  · simp [hx, Real.zero_rpow (show p - 1 ≠ 0 by linarith)]
  · calc
      ‖F x‖ * ‖F x‖ ^ (p - 2) = ‖F x‖ ^ (1 : ℝ) * ‖F x‖ ^ (p - 2) := by
        rw [Real.rpow_one]
      _ = ‖F x‖ ^ (p - 1) := by
        rw [← Real.rpow_add (norm_pos_iff.mpr hx)]
        congr 1
        ring

theorem canonicalDual_pairing (F : ℝ → ℂ) {p : ℝ} (hp : 1 < p) (x : ℝ) :
    F x * canonicalDual F p x = (‖F x‖ ^ p : ℝ) := by
  unfold canonicalDual
  rw [← mul_assoc, Complex.mul_conj']
  have hreal : ‖F x‖ ^ 2 * ‖F x‖ ^ (p - 2) = ‖F x‖ ^ p := by
    by_cases hx : F x = 0
    · simp [hx, Real.zero_rpow (show p ≠ 0 by linarith)]
    · rw [← Real.rpow_natCast, ← Real.rpow_add (norm_pos_iff.mpr hx)]
      congr 1
      push_cast
      ring
  exact_mod_cast hreal

theorem bounded_lp_power_le_one_of_simple_tests (ν : Measure ℝ) [IsFiniteMeasure ν]
    (F : ℝ → ℂ) (hF : Measurable F) {A p : ℝ} (hA : 0 ≤ A)
    (hFbound : ∀ x, ‖F x‖ ≤ A) (hp : 1 < p)
    (htest : ∀ g : SimpleFunc ℝ ℂ,
      ‖∫ x, F x * g x ∂ν‖ ≤
        (∫ x, ‖g x‖ ^ (p / (p - 1)) ∂ν) ^ (1 / (p / (p - 1)))) :
    (∫ x, ‖F x‖ ^ p ∂ν) ≤ 1 := by
  have hp0 : 0 < p := by linarith
  have hd : 0 < p - 1 := by linarith
  have hq : 0 < p / (p - 1) := div_pos hp0 hd
  have hg : Measurable (canonicalDual F p) := canonicalDual_measurable hF p
  have hgbound (x : ℝ) : ‖canonicalDual F p x‖ ≤ A ^ (p - 1) := by
    rw [canonicalDual_norm F hp]
    exact Real.rpow_le_rpow (norm_nonneg _) (hFbound x) hd.le
  have h := bounded_test_of_simple_tests ν F hF hA hFbound hq htest
    (canonicalDual F p) hg hgbound
  have hpair : (∫ x, F x * canonicalDual F p x ∂ν) =
      ((∫ x, ‖F x‖ ^ p ∂ν) : ℝ) := by
    simp_rw [canonicalDual_pairing F hp]
    exact integral_complex_ofReal (μ := ν) (f := fun x : ℝ => ‖F x‖ ^ p)
  have hgpow (x : ℝ) : ‖canonicalDual F p x‖ ^ (p / (p - 1)) = ‖F x‖ ^ p := by
    rw [canonicalDual_norm F hp, ← Real.rpow_mul (norm_nonneg _)]
    congr 1
    field_simp
  rw [hpair, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _))] at h
  simp_rw [hgpow] at h
  by_contra hnot
  have hI : 1 < ∫ x, ‖F x‖ ^ p ∂ν := lt_of_not_ge hnot
  have hexponent : 1 / (p / (p - 1)) < 1 := by
    rw [div_lt_one hq, one_lt_div hd]
    linarith
  exact (not_lt_of_ge h) (Real.rpow_lt_self_of_one_lt hI hexponent)

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
