import OAI.Geometry.IsometricImmersion.Darboux.QSpatialInductionStep

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem exists_Q_spatial_induction_offset
    (G R Z s0 M speed xl xr T lengthFloor : ℝ) (A : ℝ≥0)
    (hG : 0 ≤ G) (hR : 0 ≤ R) (hZ : 0 ≤ Z) (hs0 : 0 < s0) (hM : 0 ≤ M)
    (hspeed : 0 ≤ speed) (hT : 0 ≤ T) (hlen : 0 < lengthFloor)
    (hwidth : lengthFloor ≤ xr - xl - 2 * speed * T)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) :
    ∀ k : ℕ, ∃ H : ℝ≥0,
      ∀ (g : MetricField) (z : Coord → ℝ) (radius lo hi a b : ℝ),
      SmoothPositiveOn g (coordinateRectangle radius lo hi) →
      ContDiffOn ℝ ∞ z (coordinateRectangle radius lo hi) →
      (∀ p ∈ coordinateRectangle radius lo hi,
        (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p) →
      (∀ p ∈ coordinateRectangle radius lo hi, covHessian g z p 0 0 ≠ 0) →
      0 < radius → a ≤ b → b - a ≤ T →
      -radius < xl → xr < radius → a ∈ Ioo lo hi → b ∈ Ioo lo hi →
      QLowBounds g z (shrinkingSlab xl xr a b speed) s0 M speed →
      (∀ p ∈ shrinkingSlab xl xr a b speed, |p 0| ≤ R ∧ |p 1| ≤ R) →
      (∀ i j, CoordinateBound (fun p => g p i j) (shrinkingSlab xl xr a b speed) (k + 9) G) →
      CoordinateBound z (shrinkingSlab xl xr a b speed) 8 Z →
      (∀ p ∈ shrinkingSlab xl xr a b speed, d ≤ |(g p).det|) →
      (∀ p ∈ shrinkingSlab xl xr a b speed, c ≤ |covHessian g z p 0 0|) →
      (∀ ds : List (Fin 2), ds.length ≤ k + 8 → ∀ x ∈ Icc xl xr,
        |iteratedCoordPartial ds z (coordinatePoint x a)| ≤ (A : ℝ)) →
      ∀ t ∈ Icc a b, SpatialSliceL2Bound (spatialFirstJet z) t
        (inwardLeft xl a speed t) (inwardRight xr a speed t) (k + 7) H := by
  intro k
  induction k with
  | zero =>
      refine ⟨firstJetSliceBudget Z (xr - xl), ?_⟩
      intro g z radius lo hi a b hg hz hD hxx hradius hab habT hxl hxr ha hb
        hLow hcoords hgB hzB hdet hden hcut t ht
      apply coordinateC8_to_spatialFirstJet_L2_seven hzB hZ
        (fun x hx => point_mem_shrinkingSlab ht hx)
      unfold inwardLeft inwardRight
      have hh : 0 ≤ speed * (t - a) := mul_nonneg hspeed (sub_nonneg.mpr ht.1)
      linarith
  | succ k ih =>
      obtain ⟨Hprev, hprev⟩ := ih
      obtain ⟨Hnew, hle, hstep⟩ := exists_Q_spatial_induction_step
        G R Z s0 M speed xl xr T lengthFloor Hprev A hG hR hs0 hM hspeed hT hlen hwidth
        hd hc (k + 5) (by omega)
      refine ⟨Hnew, ?_⟩
      intro g z radius lo hi a b hg hz hD hxx hradius hab habT hxl hxr ha hb
        hLow hcoords hgB hzB hdet hden hcut t ht
      have hold : ∀ v ∈ Icc a b, SpatialSliceL2Bound (spatialFirstJet z) v
          (inwardLeft xl a speed v) (inwardRight xr a speed v) (k + 7) Hprev :=
        hprev g z radius lo hi a b hg hz hD hxx hradius hab habT hxl hxr ha hb
          hLow hcoords (fun i j => (hgB i j).mono (by omega) le_rfl) hzB hdet hden
          (fun ds hds x hx => hcut ds (by omega) x hx)
      have hnew := hstep g z radius lo hi a b hg hz hD hxx hradius hab habT hxl hxr ha hb
        hLow hcoords (fun i j => (hgB i j).mono (by omega) le_rfl) hzB hdet hden
        (fun ds hds x hx => hcut ds (by omega) x hx)
        (by simpa only [Nat.add_assoc] using hold) t ht
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using hnew

theorem exists_finite_Q_spatial_bound
    (G R Z s0 M speed xl xr T lengthFloor : ℝ) (A : ℝ≥0)
    (hG : 0 ≤ G) (hR : 0 ≤ R) (hZ : 0 ≤ Z) (hs0 : 0 < s0) (hM : 0 ≤ M)
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
      QLowBounds g z (shrinkingSlab xl xr a b speed) s0 M speed →
      (∀ p ∈ shrinkingSlab xl xr a b speed, |p 0| ≤ R ∧ |p 1| ≤ R) →
      (∀ i j, CoordinateBound (fun p => g p i j) (shrinkingSlab xl xr a b speed) (max 9 (N + 2)) G) →
      CoordinateBound z (shrinkingSlab xl xr a b speed) 8 Z →
      (∀ p ∈ shrinkingSlab xl xr a b speed, d ≤ |(g p).det|) →
      (∀ p ∈ shrinkingSlab xl xr a b speed, c ≤ |covHessian g z p 0 0|) →
      (∀ ds : List (Fin 2), ds.length ≤ max 8 (N + 1) → ∀ x ∈ Icc xl xr,
        |iteratedCoordPartial ds z (coordinatePoint x a)| ≤ (A : ℝ)) →
      ∀ t ∈ Icc a b, SpatialSliceL2Bound (spatialFirstJet z) t
        (inwardLeft xl a speed t) (inwardRight xr a speed t) N H := by
  obtain ⟨H, hH⟩ := exists_Q_spatial_induction_offset
    G R Z s0 M speed xl xr T lengthFloor A hG hR hZ hs0 hM hspeed hT hlen hwidth hd hc (N - 7)
  refine ⟨H, ?_⟩
  intro g z radius lo hi a b hg hz hD hxx hradius hab habT hxl hxr ha hb
    hLow hcoords hgB hzB hdet hden hcut t ht
  have hmetricOrder : N - 7 + 9 ≤ max 9 (N + 2) := by omega
  have hcutOrder : N - 7 + 8 ≤ max 8 (N + 1) := by omega
  have hb := hH g z radius lo hi a b hg hz hD hxx hradius hab habT hxl hxr ha hb
    hLow hcoords (fun i j => (hgB i j).mono hmetricOrder le_rfl) hzB hdet hden
    (fun ds hds x hx => hcut ds (hds.trans hcutOrder) x hx) t ht
  exact SpatialSliceL2Bound.mono_order_budget hb (by omega) le_rfl

end SmoothLocal.HighEquation

end

end OAI
