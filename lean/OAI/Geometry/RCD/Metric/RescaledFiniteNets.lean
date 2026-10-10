import OAI.Geometry.RCD.Metric.RescaledBallVolume
import OAI.Geometry.RCD.Coordinates.Proper

namespace OAI

/-! # Uniform finite nets for pointed RCD rescalings

The cardinality bound is independent of the rescaling radius and base point.
It is obtained from disjoint half-radius balls and the actual CD comparison,
so it supplies the finite-net hypothesis of pointed metric compactness.
-/

open Set Metric MeasureTheory
open scoped ENNReal NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Every fixed rescaled ball admits a uniformly bounded finite net once
the rescaled lower curvature is bounded. -/
theorem NoncollapsedRCD.rescaled_finite_nets {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) {R epsilon : ℝ}
    (hR : 0 < R) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∀ (p : X) (r : ℝ), 0 < r → -1 ≤ K*r^2 →
      ∃ s : Finset X, s.card ≤ N ∧ (s : Set X) ⊆ closedBall p (R*r) ∧
        ∀ x ∈ closedBall p (R*r), ∃ y ∈ s, dist x y < epsilon*r := by
  classical
  let := hX.properSpace hn
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  let rho := min (epsilon/2) R
  have hrho : 0 < rho := lt_min (by positivity) hR
  have hrhoR : rho ≤ R := min_le_right _ _
  have hrhoe : rho < epsilon := (min_le_left _ _).trans_lt (by linarith only [hepsilon])
  have hdelta : 0 < rho/(4*R) := div_pos hrho (by positivity)
  have hdelta1 : rho/(4*R) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith only [hrhoR, hR])
  obtain ⟨D, hD, hvolume⟩ := hX.rescaled_ball_volume_factor hn
    (a := 4*R^2) (δ := rho/(4*R)) (by positivity) hdelta hdelta1
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  refine ⟨⌈D⌉₊, ?_⟩
  intro p r hr hcurv
  let delta : ℝ≥0 := ⟨rho*r, mul_nonneg hrho.le hr.le⟩
  have hdelta0 : delta ≠ 0 := by
    apply ne_of_gt
    exact_mod_cast mul_pos hrho hr
  let s := maximalPatchNet delta (closedBall p (R*r))
  have hs : (s : Set X) ⊆ closedBall p (R*r) := maximalPatchNet_subset _ _
  let V := (hausdorff n X).real (ball p (2*R*r))
  have hV : 0 < V := ENNReal.toReal_pos
    (ne_of_gt (hX.fullSupport p (2*R*r) (by positivity)))
    (hX.finiteOnBounded _ isBounded_ball).ne
  have hc : - (4*R^2) ≤ K*(2*R*r)^2 := by
    calc
      _ ≤ (4*R^2)*(K*r^2) := by
        have hh := mul_le_mul_of_nonneg_left hcurv (by positivity : 0 ≤ 4*R^2)
        nlinarith only [hh]
      _ = _ := by ring
  have hlower (y : X) (hy : y ∈ s) :
      V/D ≤ (hausdorff n X).real (ball y ((rho*r)/2)) := by
    have hd : dist y p ≤ 2*R*r := by
      have hh : dist y p ≤ R*r := hs hy
      nlinarith only [hh, mul_pos hR hr]
    have hh := hvolume p (2*R*r) (by positivity) hc y hd
    have heq : rho/(4*R)*(2*R*r) = (rho*r)/2 := by field_simp; ring
    rw [heq] at hh
    apply (div_le_iff₀ hD0).mpr
    simpa only [V, mul_comm] using hh
  have hsep : (s : Set X).Pairwise (fun x y => rho*r ≤ dist x y) := by
    intro x hx y hy hxy
    exact (maximalPatchNet_separated delta _ hx hy hxy).le
  have hcard : (s.card : ℝ) ≤ D := by
    have hb := separated_card_mul_volume_le (hausdorff n X) s p hsep
      (fun y hy => hs hy) hlower (hX.finiteOnBounded _ isBounded_ball).ne
    have hrad : R*r + (rho*r)/2 ≤ 2*R*r := by
      have hh := mul_le_mul_of_nonneg_right hrhoR hr.le
      nlinarith only [hh, mul_pos hR hr]
    have hm := measureReal_mono (ball_subset_ball hrad)
      (hX.finiteOnBounded (ball p (2*R*r)) isBounded_ball).ne
    have hb' : (s.card:ℝ)*(V/D) ≤ V := hb.trans hm
    apply (mul_le_mul_iff_left₀ (div_pos hV hD0)).mp
    rw [mul_comm D (V/D), div_mul_cancel₀ V hD0.ne']
    exact hb'
  refine ⟨s, ?_, hs, ?_⟩
  · exact_mod_cast hcard.trans (Nat.le_ceil D)
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := maximalPatchNet_covers_bounded hdelta0 isBounded_closedBall x hx
    refine ⟨y, hy, hxy.trans_lt ?_⟩
    exact mul_lt_mul_of_pos_right hrhoe hr

end RegularPointCoordinates

end

end OAI
