import OAI.Analysis.CircleDomains.Sobolev.MetricInterpolation
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace OAI

/-! The bounded complex coefficient of a positive planar metric. This is
 the coefficient needed for the smooth metric-sphere uniformization input. -/
open Matrix
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

def metricBeltramiDenominator (A : PlanarMetric) : ℝ :=
  A 0 0 + A 1 1 + 2 * Real.sqrt A.det

def metricBeltramiCoefficient (A : PlanarMetric) : ℂ :=
  (⟨A 0 0 - A 1 1, 2 * A 0 1⟩ : ℂ) / (metricBeltramiDenominator A : ℂ)

lemma metricBeltramiDenominator_pos {A : PlanarMetric} (hA : A.PosDef) :
    0 < metricBeltramiDenominator A := by
  have h0 : 0 < A 0 0 := hA.diag_pos
  have h1 : 0 < A 1 1 := hA.diag_pos
  have hs := Real.sqrt_nonneg A.det
  dsimp [metricBeltramiDenominator]
  linarith

lemma metricBeltramiCoefficient_norm_lt_one {A : PlanarMetric} (hA : A.PosDef) :
    ‖metricBeltramiCoefficient A‖ < 1 := by
  have hsym : A 1 0 = A 0 1 := by
    have h := congrFun (congrFun hA.isHermitian.eq (0 : Fin 2)) (1 : Fin 2)
    simpa only [Matrix.conjTranspose_apply, star_trivial] using h
  have hdet : A.det = A 0 0 * A 1 1 - (A 0 1)^2 := by
    rw [Matrix.det_fin_two, hsym]
    ring
  have hd := metricBeltramiDenominator_pos hA
  have hs := Real.sqrt_pos.2 hA.det_pos
  have hsq := Real.sq_sqrt hA.det_pos.le
  have hid : (A 0 0 - A 1 1)^2 + (2 * A 0 1)^2 =
      (metricBeltramiDenominator A)^2 -
        4 * Real.sqrt A.det * metricBeltramiDenominator A := by
    dsimp [metricBeltramiDenominator]
    rw [hdet] at hsq ⊢
    nlinarith only [hsq]
  have hn : ‖metricBeltramiCoefficient A‖^2 =
      ((A 0 0 - A 1 1)^2 + (2 * A 0 1)^2) /
        (metricBeltramiDenominator A)^2 := by
    rw [metricBeltramiCoefficient, norm_div, div_pow, Complex.norm_real,
      Real.norm_eq_abs, sq_abs, Complex.sq_norm]
    simp only [Complex.normSq_apply]
    ring
  have hlt : ‖metricBeltramiCoefficient A‖^2 < 1 := by
    rw [hn, div_lt_one (sq_pos_of_pos hd), hid]
    have hpos := mul_pos hs hd
    nlinarith
  nlinarith [norm_nonneg (metricBeltramiCoefficient A)]

@[simp] lemma metricBeltramiCoefficient_scalar (r : ℝ) :
    metricBeltramiCoefficient (r • (1 : PlanarMetric)) = 0 := by
  unfold metricBeltramiCoefficient
  have hn : (⟨(r • (1 : PlanarMetric)) 0 0 - (r • (1 : PlanarMetric)) 1 1,
      2 * (r • (1 : PlanarMetric)) 0 1⟩ : ℂ) = 0 := by
    apply Complex.ext <;> simp [Matrix.smul_apply]
  rw [hn, zero_div]

lemma contDiff_metricBeltramiCoefficient
    {g : (ℝ × ℝ) → PlanarMetric} (hg : ContDiff ℝ ∞ g)
    (hPD : ∀ x, (g x).PosDef) :
    ContDiff ℝ ∞ (fun x => metricBeltramiCoefficient (g x)) := by
  have hc (i j : Fin 2) : ContDiff ℝ ∞ (fun x => g x i j) := by
    fun_prop
  have hd : ContDiff ℝ ∞ (fun x => (g x).det) := by
    simp only [Matrix.det_fin_two]
    exact ((hc 0 0).mul (hc 1 1)).sub ((hc 0 1).mul (hc 1 0))
  have hs := hd.sqrt (fun x => (hPD x).det_pos.ne')
  have hden : ContDiff ℝ ∞ (fun x => metricBeltramiDenominator (g x)) :=
    ((hc 0 0).add (hc 1 1)).add (contDiff_const.mul hs)
  have hn : ContDiff ℝ ∞ (fun x => (⟨g x 0 0 - g x 1 1, 2 * g x 0 1⟩ : ℂ)) := by
    have he (x : ℝ × ℝ) : (⟨g x 0 0 - g x 1 1, 2 * g x 0 1⟩ : ℂ) =
        ((g x 0 0 - g x 1 1 : ℝ) : ℂ) + ((2 * g x 0 1 : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    simp_rw [he]
    exact (Complex.ofRealCLM.contDiff.comp ((hc 0 0).sub (hc 1 1))).add
      ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (hc 0 1))).mul contDiff_const)
  have hinv := hden.inv (fun x => (metricBeltramiDenominator_pos (hPD x)).ne')
  simpa only [metricBeltramiCoefficient, div_eq_mul_inv, Function.comp_apply,
    Pi.inv_apply, Complex.ofRealCLM_apply, Complex.ofReal_inv]
    using hn.mul (Complex.ofRealCLM.contDiff.comp hinv)

lemma metricBeltramiCoefficient_compact_support
    {g : (ℝ × ℝ) → PlanarMetric} {R : ℝ}
    (hfar : ∀ x ∉ Metric.closedBall 0 R, ∃ r : ℝ, g x = r • 1) :
    HasCompactSupport (fun x => metricBeltramiCoefficient (g x)) := by
  apply (isCompact_closedBall (0 : ℝ × ℝ) R).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  by_contra hball
  obtain ⟨r, hr⟩ := hfar x hball
  exact hx (by simp only [hr, metricBeltramiCoefficient_scalar])

lemma metricBeltramiCoefficient_uniform_bound
    {g : (ℝ × ℝ) → PlanarMetric} (hg : ContDiff ℝ ∞ g)
    (hPD : ∀ x, (g x).PosDef) {R : ℝ} (hR : 0 < R)
    (hfar : ∀ x ∉ Metric.closedBall 0 R, ∃ r : ℝ, g x = r • 1) :
    ∃ k : ℝ≥0, k < 1 ∧ ∀ x, ‖metricBeltramiCoefficient (g x)‖ ≤ k := by
  have hc := (contDiff_metricBeltramiCoefficient hg hPD).continuous.norm
  have hne : (Metric.closedBall (0 : ℝ × ℝ) R).Nonempty :=
    ⟨0, Metric.mem_closedBall_self hR.le⟩
  obtain ⟨a, ha, hmax⟩ := (isCompact_closedBall (0 : ℝ × ℝ) R).exists_isMaxOn
    hne hc.continuousOn
  let k : ℝ≥0 := ⟨(‖metricBeltramiCoefficient (g a)‖ + 1) / 2, by positivity⟩
  have hlt := metricBeltramiCoefficient_norm_lt_one (hPD a)
  refine ⟨k, ?_, ?_⟩
  · change (‖metricBeltramiCoefficient (g a)‖ + 1) / 2 < (1 : ℝ)
    linarith
  · intro x
    change ‖metricBeltramiCoefficient (g x)‖ ≤
      (‖metricBeltramiCoefficient (g a)‖ + 1) / 2
    by_cases hx : x ∈ Metric.closedBall 0 R
    · have hb : ‖metricBeltramiCoefficient (g x)‖ ≤
          ‖metricBeltramiCoefficient (g a)‖ := hmax hx
      linarith
    · obtain ⟨r, hr⟩ := hfar x hx
      simp only [hr, metricBeltramiCoefficient_scalar, norm_zero]
      positivity

end CircleDomainRigidity

end

end OAI
