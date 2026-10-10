import OAI.Geometry.RCD.Harmonic.ActualSharpProjection

namespace OAI

/-! # A geometric smallness threshold for the actual sharp projection -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
  [IsFiniteMeasureOnCompacts (hausdorff n X)]
  {κ B J C A Cχ epsilon H D L M : ℝ}

/-- Small metric-approximation error and small total original source mass
make the constructed joint compactness error uniformly small. -/
theorem actual_projection_error_threshold (hB : 0 ≤ B) {delta : ℝ} (hdelta : 0 < delta) :
    ∃ tau : ℝ, 0 < tau ∧ ∀ d : ActualProjectionConfiguration hX κ B J C A Cχ epsilon H D L M,
      d.approximationError ≤ tau → d.totalSource ≤ tau → d.error < delta := by
  let Q := 2 * (((5 / 3 : ℝ) * (1024 : ℝ) ^ n) *
    (annularPoincareConstant K n * B / (3 / 4 * euclideanUnitVolume n)))
  have hQ : 0 ≤ Q := by
    have hp := annularPoincareConstant_pos K n
    have hv := euclideanUnitVolume_pos n
    dsimp only [Q]
    positivity
  let tau := min 1 (delta / (2 * (Q + 3)))
  have htau : 0 < tau := lt_min zero_lt_one (div_pos hdelta (by positivity))
  have htau1 : tau ≤ 1 := min_le_left _ _
  have htaud : (Q + 3) * tau ≤ delta / 2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * (Q + 3))).mp (min_le_right 1 (delta / (2 * (Q + 3))))
    change tau * (2 * (Q + 3)) ≤ delta at hh
    linarith
  refine ⟨tau, htau, ?_⟩
  intro d he ht
  have he0 := d.approximationError_pos.le
  have he1 : d.approximationError ≤ 1 := he.trans htau1
  have he2 : d.approximationError ^ 2 ≤ d.approximationError := by nlinarith
  let q := d.approximationError * (2 * (1 / 1024 : ℝ) + d.approximationError) / 2
  have hq0 : 0 ≤ q := by dsimp only [q]; positivity
  have hq : q ≤ d.approximationError := by dsimp only [q]; nlinarith only [he2, he0]
  have hq2 : q ^ 2 ≤ d.approximationError := by
    exact ((sq_le_sq₀ hq0 he0).mpr hq).trans he2
  have hsource := mul_le_mul_of_nonneg_left ht hQ
  have herr : d.error = d.approximationError + Q * d.totalSource + 2 * q ^ 2 := by
    dsimp only [ActualProjectionConfiguration.error, Q, q]
    ring
  rw [herr]
  nlinarith only [he, hsource, hq2, htaud, hdelta]

/-- The sharp bound now requires only separate geometric approximation
and original source tolerances, as supplied by the regular-neighborhood
construction. -/
theorem actual_sharp_projection_small_data
    (hhessian : LocalPoissonHessianActionInput hX)
    (hproduct : LocalPoissonGradientProductInput hX)
    (hpoincare : LocalMeanPoincareInput hX)
    (hgradient : LocalHarmonicL2GradientInput hX)
    (hcompact : LocalPoissonHarmonicCompactnessInput hX) (hn : 2 ≤ n)
    (hκ : 0 ≤ κ) (hK : -κ ≤ K) (hB : 0 ≤ B) (hJ : 0 ≤ J)
    (hCχ : 0 ≤ Cχ) (hA : 0 ≤ A) (hepsilon : 0 ≤ epsilon)
    (hH : 0 ≤ H) (hD : 0 ≤ D) (hL : 0 ≤ L) :
    ∃ P tau : ℝ, 0 < P ∧ 0 < tau ∧
      ∀ d : ActualProjectionConfiguration hX κ B J C A Cχ epsilon H D L M,
        d.approximationError ≤ tau → d.totalSource ≤ tau → d.projectionNorm ≤ P * d.source := by
  obtain ⟨P, hP, delta, hdelta, hbound⟩ := actual_sharp_projection (C := C) (M := M) hX
    hhessian hproduct hpoincare hgradient hcompact hn hκ hK hB hJ hCχ hA hepsilon hH hD hL
  obtain ⟨tau, htau, herror⟩ := actual_projection_error_threshold (hX := hX) (κ := κ) (J := J) (C := C)
    (A := A) (Cχ := Cχ) (epsilon := epsilon) (H := H) (D := D) (L := L) (M := M) hB hdelta
  exact ⟨P, tau, hP, htau, fun d he ht => hbound d (herror d he ht)⟩

end RegularPointCoordinates

end

end OAI
