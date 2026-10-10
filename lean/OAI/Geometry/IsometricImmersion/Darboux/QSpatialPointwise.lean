import OAI.Geometry.IsometricImmersion.Darboux.QSpatialFiniteInduction

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem exists_finite_Q_spatial_pointwise_bound
    (G R Z s0 M speed xl xr T lengthFloor : ℝ) (A : ℝ≥0)
    (hG : 0 ≤ G) (hR : 0 ≤ R) (hZ : 0 ≤ Z) (hs0 : 0 < s0) (hM : 0 ≤ M)
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
      QLowBounds g z (shrinkingSlab xl xr a b speed) s0 M speed →
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
  obtain ⟨H, hH⟩ := exists_finite_Q_spatial_bound
    G R Z s0 M speed xl xr T lengthFloor A hG hR hZ hs0 hM hspeed hT hlen hwidth hd hc (N + 1)
  refine ⟨Real.sqrt (2 + 1 / lengthFloor) * (H : ℝ), by positivity, ?_⟩
  intro g z radius lo hi a b hg hz hD hxx hradius hab habT hxl hxr ha hb
    hLow hcoords hgB hzB hdet hden hcut t ht x hx i n hn
  have hnorm := hH g z radius lo hi a b hg hz hD hxx hradius hab habT hxl hxr ha hb
    hLow hcoords (fun i j => (hgB i j).mono (by omega) le_rfl) hzB hdet hden
    (fun ds hds x hx => hcut ds (by omega) x hx) t ht
  have hU := coordinateRectangle_isOpen radius lo hi
  have hlength : 2 * speed * (b - a) < xr - xl := by
    have hh := mul_le_mul_of_nonneg_left habT (by positivity : 0 ≤ 2 * speed)
    linarith
  have hSU := shrinkingSlab_subset_rectangle hab hspeed hxl hxr ha hb hlength
  have hlength_t : lengthFloor ≤ inwardRight xr a speed t - inwardLeft xl a speed t := by
    unfold inwardLeft inwardRight
    have hd : t - a ≤ T := (sub_le_sub_right ht.2 a).trans habT
    have hh := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 2 * speed)
    linarith
  exact hnorm.pointwise_below_top hU (fun j => partial_contDiffOn hz hU j)
    (fun y hy => hSU (point_mem_shrinkingSlab ht hy)) hlen hlength_t i n (Nat.succ_le_succ hn) hx

end SmoothLocal.HighEquation

end

end OAI
