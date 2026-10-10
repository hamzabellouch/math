import OAI.Geometry.IsometricImmersion.Energy.MixedDerivativeL2
import OAI.Geometry.IsometricImmersion.Flows.FlowSobolev
import OAI.Geometry.IsometricImmersion.Caps.CapAreaFormula
import Mathlib.MeasureTheory.Function.L2Space

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology BigOperators ENNReal NNReal

namespace SmoothLocal.Analytic
open SmoothLocal.Geometry

theorem integral_sq_eq_eLpNorm_toReal_sq {f : Coord → ℝ} {μ : Measure Coord}
    (hf : MemLp f 2 μ) :
    (∫ p, f p ^ 2 ∂μ) = (eLpNorm f 2 μ).toReal ^ 2 := by
  calc
    (∫ p, f p ^ 2 ∂μ) = ∫ p, ‖hf.toLp f p‖ ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with p hp
      simp only [hp, Real.norm_eq_abs, sq_abs]
    _ = ∫ p, inner ℝ (hf.toLp f p) (hf.toLp f p) ∂μ := by
      simp only [real_inner_self_eq_norm_sq]
    _ = inner ℝ (hf.toLp f) (hf.toLp f) := rfl
    _ = ‖hf.toLp f‖ ^ 2 := real_inner_self_eq_norm_sq _
    _ = (eLpNorm f 2 μ).toReal ^ 2 := by
      rw [Lp.norm_def, eLpNorm_congr_ae hf.coeFn_toLp]

theorem integral_sq_le_of_eLpNorm_two_le {f : Coord → ℝ} {μ : Measure Coord}
    (hf : MemLp f 2 μ) {H : ℝ≥0} (hH : eLpNorm f 2 μ ≤ (H : ℝ≥0∞)) :
    (∫ p, f p ^ 2 ∂μ) ≤ (H : ℝ)^2 := by
  rw [integral_sq_eq_eLpNorm_toReal_sq hf]
  have h := ENNReal.toReal_mono (by simp : (H : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)) hH
  change (eLpNorm f 2 μ).toReal ≤ (H : ℝ) at h
  exact (sq_le_sq₀ ENNReal.toReal_nonneg H.2).mpr h

theorem eLpNorm_two_le_of_integral_sq_le {f : Coord → ℝ} {μ : Measure Coord}
    (hf : MemLp f 2 μ) {H : ℝ≥0} (hH : (∫ p, f p ^ 2 ∂μ) ≤ (H : ℝ)^2) :
    eLpNorm f 2 μ ≤ (H : ℝ≥0∞) := by
  apply (ENNReal.toReal_le_toReal hf.eLpNorm_ne_top (by simp)).mp
  rw [integral_sq_eq_eLpNorm_toReal_sq hf] at hH
  change (eLpNorm f 2 μ).toReal ≤ (H : ℝ)
  exact (sq_le_sq₀ ENNReal.toReal_nonneg H.2).mp hH

end SmoothLocal.Analytic

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Analytic

def CoordinateL2Bound (z : Coord → ℝ) (V : Set Coord) (N : ℕ) (H : ℝ≥0) : Prop :=
  ∀ ds : List (Fin 2), ds.length ≤ N →
    eLpNorm' (iteratedCoordPartial ds z) (2 : ℝ) (volume.restrict V) ≤ (H : ℝ≥0∞)

theorem CoordinateL2Bound.mono {z : Coord → ℝ} {V : Set Coord} {N n : ℕ} {H H' : ℝ≥0}
    (h : CoordinateL2Bound z V N H) (hn : n ≤ N) (hH : H ≤ H') :
    CoordinateL2Bound z V n H' := by
  intro ds hds
  exact (h ds (hds.trans hn)).trans (by exact_mod_cast hH)

theorem CoordinateL2Bound.restrict {z : Coord → ℝ} {V W : Set Coord} {N : ℕ} {H : ℝ≥0}
    (h : CoordinateL2Bound z V N H) (hWV : W ⊆ V) : CoordinateL2Bound z W N H := by
  intro ds hds
  exact (eLpNorm'_mono_measure _ (Measure.restrict_mono_set volume hWV)
    (by norm_num)).trans (h ds hds)

theorem CoordinateL2Bound.eLpNorm_le {z : Coord → ℝ} {V : Set Coord} {N : ℕ} {H : ℝ≥0}
    (hbound : CoordinateL2Bound z V N H) (word : List (Fin 2)) (hword : word.length ≤ N)
    (hmeas : AEStronglyMeasurable (iteratedCoordPartial word z) (volume.restrict V)) :
    eLpNorm (iteratedCoordPartial word z) 2 (volume.restrict V) ≤ (H : ℝ≥0∞) := by
  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) hmeas, ENNReal.toReal_ofNat]
  exact hbound word hword

theorem CoordinateL2Bound.memLp {z : Coord → ℝ} {U V : Set Coord} {N : ℕ} {H : ℝ≥0}
    (h : CoordinateL2Bound z V N H) (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    (hV : MeasurableSet V) (hVU : V ⊆ U) (ds : List (Fin 2)) (hds : ds.length ≤ N) :
    MemLp (iteratedCoordPartial ds z) 2 (volume.restrict V) := by
  have hmeas := ((orderedPartial_contDiffOn hz hU ds).continuousOn.mono
    hVU).aestronglyMeasurable (μ := volume) hV
  exact (h.eLpNorm_le ds hds hmeas).trans_lt (by finiteness)

theorem CoordinateL2Bound.integral_sq {z : Coord → ℝ} {U V : Set Coord} {N : ℕ} {H : ℝ≥0}
    (h : CoordinateL2Bound z V N H) (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    (hV : MeasurableSet V) (hVU : V ⊆ U) (ds : List (Fin 2)) (hds : ds.length ≤ N) :
    (∫ p in V, iteratedCoordPartial ds z p ^ 2) ≤ (H : ℝ)^2 := by
  have hmem := h.memLp hz hU hV hVU ds hds
  exact integral_sq_le_of_eLpNorm_two_le hmem (h.eLpNorm_le ds hds hmem.aestronglyMeasurable)

theorem heightStateFactor_eq_ordered (z : Coord → ℝ) (n : ℕ) (j : Fin 4) :
    heightStateFactor z n j =
      iteratedCoordPartial (heightStateSuffix j ++ List.replicate n 1) z := by
  rw [orderedPartial_append, orderedPartial_replicate_y]
  fin_cases j <;> rfl

theorem CoordinateL2Bound.heightFactors {z : Coord → ℝ} {V : Set Coord} {N : ℕ} {H : ℝ≥0}
    (h : CoordinateL2Bound z V N H) (n : ℕ) (j : Fin 4)
    (hn : n + heightStateBaseOrder j ≤ N) :
    eLpNorm' (heightStateFactor z n j) (2 : ℝ) (volume.restrict V) ≤ (H : ℝ≥0∞) := by
  rw [heightStateFactor_eq_ordered]
  apply h
  simpa only [List.length_append, List.length_replicate, heightStateSuffix_length, Nat.add_comm] using hn

theorem CoordinateL2Bound.heightFactors_of_aestronglyMeasurable
    {z : Coord → ℝ} {V : Set Coord} {N : ℕ} {H : ℝ≥0}
    (hbound : CoordinateL2Bound z V N H) (order : ℕ) (component : Fin 4)
    (horder : order + heightStateBaseOrder component ≤ N)
    (hmeas : AEStronglyMeasurable (heightStateFactor z order component) (volume.restrict V)) :
    eLpNorm (heightStateFactor z order component) 2 (volume.restrict V) ≤ (H : ℝ≥0∞) := by
  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) hmeas, ENNReal.toReal_ofNat]
  exact hbound.heightFactors order component horder

theorem coordinateBound_heightFactors {z : Coord → ℝ} {V : Set Coord} {N : ℕ} {B : ℝ}
    (h : CoordinateBound z V N B) (n : ℕ) (j : Fin 4)
    (hn : n + heightStateBaseOrder j ≤ N) :
    ∀ p ∈ V, |heightStateFactor z n j p| ≤ B := by
  rw [heightStateFactor_eq_ordered]
  apply h
  simpa only [List.length_append, List.length_replicate, heightStateSuffix_length, Nat.add_comm] using hn

end SmoothLocal.HighEquation

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Sobolev
open SmoothLocal.HighEquation

theorem closedRectangle_subset_capChartDomain
    {tl tr sb st : ℝ} (htl : -2 < tl) (htr : tr < 2) (hsb : -2 < sb) (hst : st < 2) :
    closedRectangle tl tr sb st ⊆ capChartDomain := by
  intro p hp
  exact ⟨⟨htl.trans_le hp.1.1, hp.1.2.trans_lt htr⟩,
    ⟨hsb.trans_le hp.2.1, hp.2.2.trans_lt hst⟩⟩

theorem coordinateL2Bound_to_nested_flow_coordinateBound
    {q z : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2, Y s t ∈ Icc (-3 : ℝ) 3)
    (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    {M tl tr sb st dt ds : ℝ} (hM : 0 ≤ M)
    (hq0 : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ)/100)
    (hq1 : ∀ p ∈ modelSquare, |coordPartial 1 q p| ≤ M)
    (htl : -2 < tl) (htr : tr < 2) (hsb : -2 < sb) (hst : st < 2)
    (hdt : 0 < dt) (hds : 0 < ds) (hz : ContDiffOn ℝ ∞ z U)
    {n : ℕ} {H : ℝ≥0}
    (hL : CoordinateL2Bound z (capChart Y '' closedRectangle tl tr sb st) (n + 2) H) :
    CoordinateBound z
      (capChart Y '' closedRectangle (tl+dt) (tr-dt) (sb+ds) (st-ds)) n
      ((squareSobolevWeight (flowInteriorRadius M dt ds)+1)*(H : ℝ)) := by
  let V := capChart Y '' closedRectangle tl tr sb st
  have hVU : V ⊆ U := actual_closed_flow_rectangle_subset_domain hSU hrange htl htr hsb hst
  have hYs := cap_flow_joint_contDiffOn hq hU hSU hY hrange hstart hode
  have hcompact : IsCompact V := (capRectangle_isCompact tl tr sb st).image_of_continuousOn
    ((capChart_contDiffOn hYs).continuousOn.mono
      (closedRectangle_subset_capChartDomain htl htr hsb hst))
  have hV : MeasurableSet V := hcompact.isClosed.measurableSet
  intro word hword p hp
  have h0 := hL.memLp hz hU hV hVU word (by omega)
  have hx := hL.memLp hz hU hV hVU (0 :: word) (by simp only [List.length_cons]; omega)
  have hy := hL.memLp hz hU hV hVU (1 :: word) (by simp only [List.length_cons]; omega)
  have hxy := hL.memLp hz hU hV hVU (1 :: 0 :: word) (by simp only [List.length_cons]; omega)
  have hpoint := actual_flow_interior_sobolev hq hU hSU hY hrange hstart hode hM hq0 hq1
    htl htr hsb hst hdt hds (orderedPartial_contDiffOn hz hU word) h0 hx hy hxy hp
  exact abs_bound_of_regionSobolevEnergy (flowInteriorRadius_pos M hdt hds) H.2 hpoint
    (hL.integral_sq hz hU hV hVU word (by omega))
    (hL.integral_sq hz hU hV hVU (0 :: word) (by simp only [List.length_cons]; omega))
    (hL.integral_sq hz hU hV hVU (1 :: word) (by simp only [List.length_cons]; omega))
    (hL.integral_sq hz hU hV hVU (1 :: 0 :: word) (by simp only [List.length_cons]; omega))

end SmoothLocal.Flow

end

end OAI
