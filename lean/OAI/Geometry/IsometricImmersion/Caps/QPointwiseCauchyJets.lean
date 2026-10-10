import OAI.Geometry.IsometricImmersion.Darboux.QFiniteActual
import OAI.Geometry.IsometricImmersion.Taylor.TaylorCauchyData

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix NNReal

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation SmoothLocal.ODE
open SmoothLocal.Weighted SmoothLocal.Hyperbolic

theorem coordinatePoint_eq_vector (x t : ℝ) : coordinatePoint x t = (![x,t] : Coord) := by
  ext i
  fin_cases i <;> simp [coordinatePoint]

theorem cauchyVelocity_iteratedDeriv {z : Coord → ℝ} {U : Set Coord}
    (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U) {x t : ℝ}
    (hp : coordinatePoint x t ∈ U) (n : ℕ) :
    iteratedDeriv n (heightCauchyVelocity z t) x =
      spatialJet (spatialFirstJet z 1) n (coordinatePoint x t) := by
  have he : heightCauchyVelocity z t = (fun y => coordPartial 1 z (coordinatePoint y t)) := by
    funext y
    rw [coordinatePoint_eq_vector]
    rfl
  rw [he, horizontalJet_slice hU (partial_contDiffOn hz hU 1) t n x hp,
    horizontalJet_eq_spatialJet]
  rfl

theorem cauchyValue_iteratedDeriv_succ {z : Coord → ℝ} {U : Set Coord}
    (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U) {x t : ℝ}
    (hp : coordinatePoint x t ∈ U) (n : ℕ) :
    iteratedDeriv (n+1) (heightCauchyValue z t) x =
      spatialJet (spatialFirstJet z 0) n (coordinatePoint x t) := by
  have he : heightCauchyValue z t = (fun y => z (coordinatePoint y t)) := by
    funext y
    rw [coordinatePoint_eq_vector]
    rfl
  rw [he, horizontalJet_slice hU hz t (n+1) x hp]
  change coordPartial 0 (horizontalJet z n) (coordinatePoint x t) = _
  rw [← horizontalJet_coordPartial hU hz 0 n _ hp, horizontalJet_eq_spatialJet]
  rfl

theorem cauchy_fullJets_of_actual_spatial_firstJets
    {z : Coord → ℝ} {U : Set Coord} (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    {x t : ℝ} (hp : coordinatePoint x t ∈ U) {N : ℕ} {Z B : ℝ}
    (hvalue : |z (coordinatePoint x t)| ≤ Z)
    (hspatial : ∀ i : Fin 2, ∀ n ≤ N,
      |spatialJet (spatialFirstJet z i) n (coordinatePoint x t)| ≤ B) :
    ∀ n ≤ N,
      ‖iteratedFDeriv ℝ n (heightCauchyValue z t) x‖ ≤ max Z B ∧
      ‖iteratedFDeriv ℝ n (heightCauchyVelocity z t) x‖ ≤ max Z B := by
  intro n hn
  constructor
  · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    cases n with
    | zero =>
      change |z ![x,t]| ≤ _
      rw [← coordinatePoint_eq_vector]
      exact hvalue.trans (le_max_left _ _)
    | succ n =>
      rw [cauchyValue_iteratedDeriv_succ hz hU hp n]
      exact (hspatial 0 n (by omega)).trans (le_max_right _ _)
  · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
      cauchyVelocity_iteratedDeriv hz hU hp n]
    exact (hspatial 1 n hn).trans (le_max_right _ _)

theorem exists_finite_actual_Q_cauchy_fullJet_bound
    (G R Z s0 speed xl xr T lengthFloor : ℝ) (A : ℝ≥0)
    (hG : 0 ≤ G) (hR : 0 ≤ R) (hZ : 0 ≤ Z) (hs0 : 0 < s0)
    (hspeed : 0 ≤ speed) (hT : 0 ≤ T) (hlen : 0 < lengthFloor)
    (hwidth : lengthFloor ≤ xr - xl - 2*speed*T)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (g : MetricField) (z : Coord → ℝ) (radius lo hi a b : ℝ),
      SmoothPositiveOn g (coordinateRectangle radius lo hi) →
      ContDiffOn ℝ ∞ z (coordinateRectangle radius lo hi) →
      (∀ p ∈ coordinateRectangle radius lo hi,
        (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p) →
      (∀ p ∈ coordinateRectangle radius lo hi, covHessian g z p 0 0 ≠ 0) →
      0 < radius → a ≤ b → b-a ≤ T →
      -radius < xl → xr < radius → a ∈ Ioo lo hi → b ∈ Ioo lo hi →
      (∀ p ∈ shrinkingSlab xl xr a b speed, s0 ≤ heightQCoefficient g z 5 p) →
      (∀ p ∈ shrinkingSlab xl xr a b speed,
        |heightQCoefficient g z 4 p| + Real.sqrt (heightQCoefficient g z 5 p) ≤ speed) →
      (∀ p ∈ shrinkingSlab xl xr a b speed, |p 0| ≤ R ∧ |p 1| ≤ R) →
      (∀ i j, CoordinateBound (fun p => g p i j) (shrinkingSlab xl xr a b speed) (max 9 (N+3)) G) →
      CoordinateBound z (shrinkingSlab xl xr a b speed) 8 Z →
      (∀ p ∈ shrinkingSlab xl xr a b speed, d ≤ |(g p).det|) →
      (∀ p ∈ shrinkingSlab xl xr a b speed, c ≤ |covHessian g z p 0 0|) →
      (∀ ds : List (Fin 2), ds.length ≤ max 8 (N+2) → ∀ x ∈ Icc xl xr,
        |iteratedCoordPartial ds z (coordinatePoint x a)| ≤ (A : ℝ)) →
      ∀ t ∈ Icc a b, ∀ x ∈ Icc (inwardLeft xl a speed t) (inwardRight xr a speed t),
        ∀ n ≤ N,
          ‖iteratedFDeriv ℝ n (heightCauchyValue z t) x‖ ≤ B ∧
          ‖iteratedFDeriv ℝ n (heightCauchyVelocity z t) x‖ ≤ B := by
  obtain ⟨B0, _, hpoint⟩ := exists_finite_actual_Q_spatial_pointwise_bound
    G R Z s0 speed xl xr T lengthFloor A hG hR hZ hs0 hspeed hT hlen hwidth hd hc N
  refine ⟨max Z B0, hZ.trans (le_max_left _ _), ?_⟩
  intro g z radius lo hi a b hg hz hD hxx hradius hab habT hxl hxr ha hb
    hs hchar hcoords hgB hzB hdet hden hcut t ht x hx n hn
  have hU := coordinateRectangle_isOpen radius lo hi
  have hlength : 2*speed*(b-a) < xr-xl := by
    have hh := mul_le_mul_of_nonneg_left habT (by positivity : 0 ≤ 2*speed)
    linarith
  have hSU := shrinkingSlab_subset_rectangle hab hspeed hxl hxr ha hb hlength
  have hpS := point_mem_shrinkingSlab ht hx
  have hp := hSU hpS
  have hv : |z (coordinatePoint x t)| ≤ Z := hzB [] (by norm_num) _ hpS
  exact cauchy_fullJets_of_actual_spatial_firstJets hz hU hp hv
    (hpoint g z radius lo hi a b hg hz hD hxx hradius hab habT hxl hxr ha hb
      hs hchar hcoords hgB hzB hdet hden hcut t ht x hx) n hn

theorem halfWidth_mem_inward_interval {L r t x : ℝ} (hL : 0 < L) (hr : 0 < r)
    (ht : t ∈ Icc (-r) 0) (hx : |x| ≤ L*r/2) :
    x ∈ Icc (inwardLeft (-(L*r)) (-r) (L/4) t)
      (inwardRight (L*r) (-r) (L/4) t) := by
  have hLr : 0 < L*r := mul_pos hL hr
  have hprod := mul_nonpos_of_nonneg_of_nonpos hL.le ht.2
  obtain ⟨hxl,hxr⟩ := abs_le.mp hx
  unfold inwardLeft inwardRight
  constructor <;> nlinarith

end SmoothLocal.Taylor

end

end OAI
