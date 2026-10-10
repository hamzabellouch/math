import OAI.Geometry.IsometricImmersion.Darboux.QLowActualBounds
import OAI.Geometry.IsometricImmersion.Darboux.QSpatialPointwise

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem exists_finite_actual_Q_spatial_bound
    (G R Z s0 speed xl xr T lengthFloor : ℝ) (A : ℝ≥0)
    (hG : 0 ≤ G) (hR : 0 ≤ R) (hZ : 0 ≤ Z) (hs0 : 0 < s0)
    (hspeed : 0 ≤ speed) (hT : 0 ≤ T) (hlen : 0 < lengthFloor)
    (hwidth : lengthFloor ≤ xr - xl - 2 * speed * T)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) (N : ℕ) :
    ∃ H : ℝ≥0,
      ∀ (g : MetricField) (z : Coord → ℝ) (radius lo hi a b : ℝ),
      SmoothPositiveOn g (coordinateRectangle radius lo hi) →
      ContDiffOn ℝ ∞ z (coordinateRectangle radius lo hi) →
      (∀ p ∈ coordinateRectangle radius lo hi,
        (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p) →
      (∀ p ∈ coordinateRectangle radius lo hi, covHessian g z p 0 0 ≠ 0) →
      0 < radius → a ≤ b → b - a ≤ T →
      -radius < xl → xr < radius → a ∈ Ioo lo hi → b ∈ Ioo lo hi →
      (∀ p ∈ shrinkingSlab xl xr a b speed, s0 ≤ heightQCoefficient g z 5 p) →
      (∀ p ∈ shrinkingSlab xl xr a b speed,
        |heightQCoefficient g z 4 p| + Real.sqrt (heightQCoefficient g z 5 p) ≤ speed) →
      (∀ p ∈ shrinkingSlab xl xr a b speed, |p 0| ≤ R ∧ |p 1| ≤ R) →
      (∀ i j, CoordinateBound (fun p => g p i j) (shrinkingSlab xl xr a b speed) (max 9 (N + 2)) G) →
      CoordinateBound z (shrinkingSlab xl xr a b speed) 8 Z →
      (∀ p ∈ shrinkingSlab xl xr a b speed, d ≤ |(g p).det|) →
      (∀ p ∈ shrinkingSlab xl xr a b speed, c ≤ |covHessian g z p 0 0|) →
      (∀ ds : List (Fin 2), ds.length ≤ max 8 (N + 1) → ∀ x ∈ Icc xl xr,
        |iteratedCoordPartial ds z (coordinatePoint x a)| ≤ (A : ℝ)) →
      ∀ t ∈ Icc a b, SpatialSliceL2Bound (spatialFirstJet z) t
        (inwardLeft xl a speed t) (inwardRight xr a speed t) N H := by
  obtain ⟨M, hM, hlow⟩ := exists_actual_QLowBounds G R Z hG hR hd hc
  obtain ⟨H, hbound⟩ := exists_finite_Q_spatial_bound
    G R Z s0 M speed xl xr T lengthFloor A hG hR hZ hs0 hM hspeed hT hlen hwidth hd hc N
  refine ⟨H, ?_⟩
  intro g z radius lo hi a b hg hz hD hxx hradius hab habT hxl hxr ha hb
    hs hchar hcoords hgB hzB hdet hden hcut
  have hlength : 2 * speed * (b - a) < xr - xl := by
    have hh := mul_le_mul_of_nonneg_left habT (by positivity : 0 ≤ 2 * speed)
    linarith
  have hSU := shrinkingSlab_subset_rectangle hab hspeed hxl hxr ha hb hlength
  have hLow := hlow g z (coordinateRectangle radius lo hi) (shrinkingSlab xl xr a b speed)
    hg (coordinateRectangle_isOpen radius lo hi) hz hSU hcoords
    (fun i j => (hgB i j).mono (by omega) le_rfl)
    (hzB.mono (by norm_num) le_rfl) hdet hden s0 speed hs hchar
  exact hbound g z radius lo hi a b hg hz hD hxx hradius hab habT hxl hxr ha hb
    hLow hcoords hgB hzB hdet hden hcut

theorem exists_finite_actual_Q_spatial_pointwise_bound
    (G R Z s0 speed xl xr T lengthFloor : ℝ) (A : ℝ≥0)
    (hG : 0 ≤ G) (hR : 0 ≤ R) (hZ : 0 ≤ Z) (hs0 : 0 < s0)
    (hspeed : 0 ≤ speed) (hT : 0 ≤ T) (hlen : 0 < lengthFloor)
    (hwidth : lengthFloor ≤ xr - xl - 2 * speed * T)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (g : MetricField) (z : Coord → ℝ) (radius lo hi a b : ℝ),
      SmoothPositiveOn g (coordinateRectangle radius lo hi) →
      ContDiffOn ℝ ∞ z (coordinateRectangle radius lo hi) →
      (∀ p ∈ coordinateRectangle radius lo hi,
        (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p) →
      (∀ p ∈ coordinateRectangle radius lo hi, covHessian g z p 0 0 ≠ 0) →
      0 < radius → a ≤ b → b - a ≤ T →
      -radius < xl → xr < radius → a ∈ Ioo lo hi → b ∈ Ioo lo hi →
      (∀ p ∈ shrinkingSlab xl xr a b speed, s0 ≤ heightQCoefficient g z 5 p) →
      (∀ p ∈ shrinkingSlab xl xr a b speed,
        |heightQCoefficient g z 4 p| + Real.sqrt (heightQCoefficient g z 5 p) ≤ speed) →
      (∀ p ∈ shrinkingSlab xl xr a b speed, |p 0| ≤ R ∧ |p 1| ≤ R) →
      (∀ i j, CoordinateBound (fun p => g p i j) (shrinkingSlab xl xr a b speed) (max 9 (N + 3)) G) →
      CoordinateBound z (shrinkingSlab xl xr a b speed) 8 Z →
      (∀ p ∈ shrinkingSlab xl xr a b speed, d ≤ |(g p).det|) →
      (∀ p ∈ shrinkingSlab xl xr a b speed, c ≤ |covHessian g z p 0 0|) →
      (∀ ds : List (Fin 2), ds.length ≤ max 8 (N + 2) → ∀ x ∈ Icc xl xr,
        |iteratedCoordPartial ds z (coordinatePoint x a)| ≤ (A : ℝ)) →
      ∀ t ∈ Icc a b, ∀ x ∈ Icc (inwardLeft xl a speed t) (inwardRight xr a speed t),
        ∀ i : Fin 2, ∀ n ≤ N,
          |spatialJet (spatialFirstJet z i) n (coordinatePoint x t)| ≤ B := by
  obtain ⟨M, hM, hlow⟩ := exists_actual_QLowBounds G R Z hG hR hd hc
  obtain ⟨B, hB, hbound⟩ := exists_finite_Q_spatial_pointwise_bound
    G R Z s0 M speed xl xr T lengthFloor A hG hR hZ hs0 hM hspeed hT hlen hwidth hd hc N
  refine ⟨B, hB, ?_⟩
  intro g z radius lo hi a b hg hz hD hxx hradius hab habT hxl hxr ha hb
    hs hchar hcoords hgB hzB hdet hden hcut
  have hlength : 2 * speed * (b - a) < xr - xl := by
    have hh := mul_le_mul_of_nonneg_left habT (by positivity : 0 ≤ 2 * speed)
    linarith
  have hSU := shrinkingSlab_subset_rectangle hab hspeed hxl hxr ha hb hlength
  have hLow := hlow g z (coordinateRectangle radius lo hi) (shrinkingSlab xl xr a b speed)
    hg (coordinateRectangle_isOpen radius lo hi) hz hSU hcoords
    (fun i j => (hgB i j).mono (by omega) le_rfl)
    (hzB.mono (by norm_num) le_rfl) hdet hden s0 speed hs hchar
  exact hbound g z radius lo hi a b hg hz hD hxx hradius hab habT hxl hxr ha hb
    hLow hcoords hgB hzB hdet hden hcut

end SmoothLocal.HighEquation

end

end OAI
