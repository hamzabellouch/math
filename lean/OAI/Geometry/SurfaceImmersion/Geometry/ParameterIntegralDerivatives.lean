import OAI.Geometry.SurfaceImmersion.Correction.SmoothParameterIntegral
import OAI.Geometry.Immersion.ClosedSurface.WeightedBounds

namespace OAI

/-! Every parameter derivative commutes with a compact interval integral.
This supplies the weighted bounds for periodic means and primitives. -/
noncomputable section
open MeasureTheory
open scoped ContDiff

universe u
namespace ClosedSurfaceR4.SmoothParameterIntegral

variable {P E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def partialIterated (n : ℕ) (F : P × ℝ → E) (z : P × ℝ) : P [×n]→L[ℝ] E :=
  iteratedFDeriv ℝ n (fun p => F (p, z.2)) z.1

omit [FiniteDimensional ℝ P] [CompleteSpace E] in
lemma partialIterated_succ {F : P × ℝ → E} (n : ℕ)
    (h : ContDiff ℝ ∞ (partialIterated n F)) :
    partialIterated (n + 1) F = fun z =>
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => P) E).symm
        (partialDerivative (partialIterated n F) z) := by
  funext z
  change (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => P) E).symm
    (fderiv ℝ (fun p => partialIterated n F (p, z.2)) z.1) = _
  rw [(partial_hasFDerivAt h z.1 z.2).fderiv]

omit [FiniteDimensional ℝ P] [CompleteSpace E] in
lemma contDiff_partialIterated {F : P × ℝ → E} (hF : ContDiff ℝ ∞ F) (n : ℕ) :
    ContDiff ℝ ∞ (partialIterated n F) := by
  induction n with
  | zero =>
    exact (continuousMultilinearCurryFin0 ℝ P E).symm.contDiff.comp hF
  | succ n ih =>
    rw [partialIterated_succ n ih]
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => P) E).symm.contDiff.comp
      (contDiff_partialDerivative ih)

/-- The actual all-order derivative formula, with no separate derivative
interchange hypothesis. -/
theorem iteratedFDeriv_integral {F : P × ℝ → E} (hF : ContDiff ℝ ∞ F)
    (a b : ℝ) (n : ℕ) (p : P) :
    iteratedFDeriv ℝ n (fun q => ∫ t in a..b, F (q, t)) p =
      ∫ t in a..b, partialIterated n F (p, t) := by
  induction n generalizing p with
  | zero =>
    let L : E →L[ℝ] (P [×0]→L[ℝ] E) :=
      (continuousMultilinearCurryFin0 ℝ P E).symm.toContinuousLinearEquiv.toContinuousLinearMap
    change L (∫ t in a..b, F (p, t)) = ∫ t in a..b, L (F (p, t))
    exact (L.intervalIntegral_comp_comm
      ((hF.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b)).symm
  | succ n ih =>
    let L : (P →L[ℝ] P [×n]→L[ℝ] E) →L[ℝ] (P [×(n + 1)]→L[ℝ] E) :=
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => P) E).symm.toContinuousLinearEquiv.toContinuousLinearMap
    have hFn := contDiff_partialIterated hF n
    have he : iteratedFDeriv ℝ n (fun q => ∫ t in a..b, F (q, t)) =
        fun q => ∫ t in a..b, partialIterated n F (q, t) := funext ih
    change L (fderiv ℝ (iteratedFDeriv ℝ n (fun q => ∫ t in a..b, F (q, t))) p) = _
    rw [he, (hasFDerivAt_integral hFn a b p).fderiv]
    have hInt : IntervalIntegrable (fun t => partialDerivative (partialIterated n F) (p, t))
        volume a b := ((contDiff_partialDerivative hFn).continuous.comp
          (continuous_const.prodMk continuous_id)).intervalIntegrable a b
    rw [← L.intervalIntegral_comp_comm hInt]
    apply intervalIntegral.integral_congr
    intro t _
    exact (congrFun (partialIterated_succ n hFn) (p, t)).symm

end ClosedSurfaceR4.SmoothParameterIntegral
namespace ClosedSurfaceR4.WeightedEstimates
open SmoothParameterIntegral

variable {P E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Parameter integration preserves every weighted derivative bound, with
only the length of the integration interval as an operator bound. -/
theorem weighted_parameter_integral {F : P × ℝ → E} (hF : ContDiff ℝ ∞ F)
    {U : Set P} (hU : IsOpen U) {s C : ℝ} (hs : 0 < s) (m : ℕ) (a b : ℝ)
    (hb : ∀ j ≤ m, ∀ p ∈ U, ∀ t ∈ Set.uIcc a b,
      s ^ j * ‖partialIterated j F (p, t)‖ ≤ C) :
    WeightedBound U s m (C * |b - a|) (fun p => ∫ t in a..b, F (p, t)) := by
  have hI := contDiff_integral hF a b
  intro j hj p hp
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn
    ((hI.of_le (by simp : (j : ℕ∞ω) ≤ ∞)).contDiffAt) hp,
    iteratedFDeriv_integral hF]
  have hn : ‖∫ t in a..b, partialIterated j F (p, t)‖ ≤ C / s ^ j * |b - a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    exact (le_div_iff₀ (pow_pos hs j)).mpr (by
      simpa only [mul_comm] using hb j hj p hp t (Set.uIoc_subset_uIcc ht))
  calc
    s ^ j * ‖∫ t in a..b, partialIterated j F (p, t)‖ ≤
        s ^ j * (C / s ^ j * |b - a|) :=
      mul_le_mul_of_nonneg_left hn (pow_nonneg hs.le j)
    _ = C * |b - a| := by field_simp [hs.ne']

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
