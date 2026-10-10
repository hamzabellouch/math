import OAI.Geometry.RCD.Coordinates.FullSplittingCoordinates
import OAI.Geometry.RCD.Coordinates.RegularLargeGoodSets

namespace OAI

/-! # All-scale coordinates on the actual regular harmonic good sets

Only the original Huang--Huang product input remains conditional here.
The family and compact good set are constructed from the actual space.
-/

open Set Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.regular_good_coordinate_sets {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    (hpublished : LocalAlmostSplittingInput hX) {p : X} (hp : IsRegular n p)
    {η ζ : ℝ} (hη : 0 < η) (hζ : 0 < ζ) :
    ∃ t s : ℝ, 0 < t ∧ 0 < s ∧ ∀ R : ℝ, 0 < R → R < s →
      ∃ (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
        (v : X → Euclidean n) (U : Set X),
        FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (2*R) t u v ∧
        IsCompact U ∧ U ⊆ closedBall p R ∧
        (hausdorff n X).real (ball p R \ U) ≤ ζ*(hausdorff n X).real (ball p R) ∧
        ∀ x ∈ U, ∀ r : ℝ, 0 < r → r < R/16 →
          IsPointedApproximation x 0 r (1/16) η (fun z => r⁻¹ • (v z-v x)) := by
  obtain ⟨ε,he,hcoord⟩ := hX.full_splitting_coordinates hn hpublished hη
  let t := min ε 1
  have ht : 0 < t := lt_min he zero_lt_one
  have htε : t ≤ ε := min_le_left _ _
  obtain ⟨s,hs,hgood⟩ := hX.regular_large_good_sets hn hp ht hζ
  let S := min s (min 1 (ε/(|K|+1)))
  have hS : 0 < S := lt_min hs (lt_min zero_lt_one (by positivity))
  refine ⟨t,S,ht,hS,?_⟩
  intro R hR hRS
  have hRs : R < s := hRS.trans_le (min_le_left _ _)
  have hR1 : R ≤ 1 := (hRS.le.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hRe : R ≤ ε/(|K|+1) :=
    (hRS.le.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hKR : |K| * R ≤ ε := by
    have hh := (le_div_iff₀ (by positivity : 0 < |K|+1)).mp hRe
    nlinarith only [hh,hR]
  obtain ⟨u,v,U,hsplit,hU,hUsub,hbad,hall⟩ := hgood R hR hRs
  refine ⟨u,v,U,hsplit,hU,hUsub,hbad,?_⟩
  intro x hx r hr hrR
  have hrR' : r < R := by linarith only [hrR,hR]
  have hrsq : r^2 ≤ R := by nlinarith only [hrR',hr,hR1,hR]
  have hcurv : -ε ≤ K*r^2 := by
    have h1 := mul_le_mul_of_nonneg_left hrsq (abs_nonneg K)
    have h2 := mul_le_mul_of_nonneg_right (neg_abs_le K) (sq_nonneg r)
    linarith only [h1,h2,hKR]
  exact hcoord x r hr hcurv u v
    ((hall x hx (16*r) (by positivity) (by linarith only [hrR])).mono_error _ _ ht.le htε)

end RegularPointCoordinates

end

end OAI
