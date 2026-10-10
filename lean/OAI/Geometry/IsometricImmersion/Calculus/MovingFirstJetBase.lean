import OAI.Geometry.IsometricImmersion.Energy.MovingIntervalSourceL2
import OAI.Geometry.IsometricImmersion.Calculus.CoordinateJetBounds
import Mathlib.Analysis.Calculus.FDeriv.Measurable

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval ENNReal NNReal

namespace SmoothLocal.Hyperbolic
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE

def spatialFirstJet (z : Coord → ℝ) (i : Fin 2) : Coord → ℝ := coordPartial i z

theorem spatialJet_firstJet_eq_word (z : Coord → ℝ) (n : ℕ) (i : Fin 2) :
    spatialJet (spatialFirstJet z i) n =
      iteratedCoordPartial (List.replicate n 0 ++ [i]) z := by
  induction n with
  | zero => rfl
  | succ n hn =>
      simp only [spatialJet, List.replicate_succ, List.cons_append, iteratedCoordPartial, hn]

theorem coordinateBound_spatialFirstJet
    {z : Coord → ℝ} {V : Set Coord} {N n : ℕ} {Z : ℝ}
    (hz : CoordinateBound z V (N + 1) Z) (hn : n ≤ N) (i : Fin 2) {p : Coord} (hp : p ∈ V) :
    |spatialJet (spatialFirstJet z i) n p| ≤ Z := by
  rw [spatialJet_firstJet_eq_word]
  apply hz _ _ p hp
  simp only [List.length_append, List.length_replicate, List.length_singleton]
  omega

def firstJetSliceBudget (Z widthUpper : ℝ) : ℝ≥0 :=
  (‖Z‖ₑ * (ENNReal.ofReal widthUpper) ^ (1 / (2 : ℝ))).toNNReal

theorem firstJetSliceBudget_coe (Z widthUpper : ℝ) :
    (firstJetSliceBudget Z widthUpper : ℝ≥0∞) =
      ‖Z‖ₑ * (ENNReal.ofReal widthUpper) ^ (1 / (2 : ℝ)) := by
  exact ENNReal.coe_toNNReal (by finiteness)

theorem coordinateBound_to_spatialFirstJet_L2
    {z : Coord → ℝ} {V : Set Coord} {theta left right Z widthUpper : ℝ} {N : ℕ}
    (hz : CoordinateBound z V (N + 1) Z) (hZ : 0 ≤ Z)
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ V)
    (hwidth : right - left ≤ widthUpper) :
    SpatialSliceL2Bound (spatialFirstJet z) theta left right N
      (firstJetSliceBudget Z widthUpper) := by
  intro i n hn
  have hmeas : Measurable (spatialJet (spatialFirstJet z i) n) := by
    cases n with
    | zero => exact measurable_fderiv_apply_const ℝ z (Pi.single i 1)
    | succ order =>
        exact measurable_fderiv_apply_const ℝ
          (spatialJet (spatialFirstJet z i) order) (Pi.single 0 1)
  have hpoint : Continuous (fun x : ℝ => coordinatePoint x theta) := by
    unfold coordinatePoint
    fun_prop
  have hdom : ∀ᵐ x ∂volume.restrict (Icc left right),
      ‖spatialJet (spatialFirstJet z i) n (coordinatePoint x theta)‖ ≤ ‖Z‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [Real.norm_eq_abs, Real.norm_of_nonneg hZ]
    exact coordinateBound_spatialFirstJet hz hn i (hseg x hx)
  have hvol : volume (Icc left right) ≤ ENNReal.ofReal widthUpper := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_le_ofReal hwidth
  calc
    _ ≤ eLpNorm (fun _ : ℝ => Z) 2 (volume.restrict (Icc left right)) :=
      eLpNorm_mono_ae (hmeas.comp hpoint.measurable).aestronglyMeasurable hdom
    _ = ‖Z‖ₑ * (volume (Icc left right)) ^ (1 / (2 : ℝ)) := by
      rw [eLpNorm_const' Z (by norm_num) (by norm_num)]
      simp only [Measure.restrict_apply_univ, ENNReal.toReal_ofNat]
    _ ≤ ‖Z‖ₑ * (ENNReal.ofReal widthUpper) ^ (1 / (2 : ℝ)) :=
      mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hvol (by norm_num))
    _ = _ := (firstJetSliceBudget_coe Z widthUpper).symm

theorem coordinateC8_to_spatialFirstJet_L2_seven
    {z : Coord → ℝ} {V : Set Coord} {theta left right Z widthUpper : ℝ}
    (hz : CoordinateBound z V 8 Z) (hZ : 0 ≤ Z)
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ V)
    (hwidth : right - left ≤ widthUpper) :
    SpatialSliceL2Bound (spatialFirstJet z) theta left right 7
      (firstJetSliceBudget Z widthUpper) :=
  coordinateBound_to_spatialFirstJet_L2 hz hZ hseg hwidth

theorem spatialFirstJet_slice_memLp_two
    {z : Coord → ℝ} {U : Set Coord} {theta left right : ℝ}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ U) (i : Fin 2) (n : ℕ) :
    MemLp (fun x => spatialJet (spatialFirstJet z i) n (coordinatePoint x theta)) 2
      (volume.restrict (Icc left right)) :=
  smooth_slice_memLp_two
    (spatialJet_contDiffOn hU (partial_contDiffOn hz hU i) n).continuousOn hseg

end SmoothLocal.Hyperbolic

end

end OAI
