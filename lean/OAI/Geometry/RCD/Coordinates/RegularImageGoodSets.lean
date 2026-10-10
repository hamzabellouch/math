import OAI.Geometry.RCD.Coordinates.RegularBoundedCoarseFineSets
import OAI.Geometry.RCD.Coordinates.CoarseFineCoordinateDistance
import OAI.Geometry.RCD.Coordinates.SplittingCoordinateLipschitz

namespace OAI

/-! # One harmonic good set retains the data for the image-volume argument -/

open Set Metric MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.regular_image_good_sets {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    (hpublished : LocalAlmostSplittingInput hX) {p : X} (hp : IsRegular n p)
    {η ζ : ℝ} (hη : 0 < η) (hζ : 0 < ζ) :
    ∃ s : ℝ, 0 < s ∧ ∀ R : ℝ, 0 < R → R < s →
      ∃ (v : X → Euclidean n) (U : Set X),
        IsCompact U ∧ U ⊆ closedBall p R ∧
        (hausdorff n X).real (ball p R \ U) ≤ ζ*(hausdorff n X).real (ball p (16*R)) ∧
        LipschitzOnWith ⟨1+32*η,by positivity⟩ v U ∧
        LipschitzOnWith ⟨2*(n:ℝ),by positivity⟩ v (ball p (4*R)) ∧
        IsPointedApproximation p 0 (2*R) (1/2) (η/4)
          (fun x => (2*R)⁻¹ • (v x-v p)) ∧
        ∀ x ∈ U, ∀ r : ℝ, 0 < r → r < R →
          IsPointedApproximation x 0 r (1/16) η (fun z => r⁻¹ • (v z-v x)) := by
  obtain ⟨t,s,ht,ht1,hs,hsets⟩ := hX.regular_bounded_coarse_fine_sets hn hpublished hp hη hζ
  refine ⟨s/16,by positivity,?_⟩
  intro R hR hRs
  obtain ⟨u,v,V,hsplit,hV,hVsub,hbad,hcoarse,hfine⟩ := hsets (16*R) (by positivity)
    (by linarith only [hRs])
  let U := V ∩ closedBall p R
  have hU : IsCompact U := hV.inter_right isClosed_closedBall
  have hUsub : U ⊆ closedBall p R := inter_subset_right
  have hc : IsPointedApproximation p 0 (2*R) (1/2) (η/4)
      (fun x => (2*R)⁻¹ • (v x-v p)) := by
    simpa only [show 16*R/8=2*R by ring] using hcoarse
  have hf : ∀ x ∈ U, ∀ r : ℝ, 0 < r → r < R →
      IsPointedApproximation x 0 r (1/16) η (fun z => r⁻¹ • (v z-v x)) := by
    intro x hx r hr hrR
    exact hfine x hx.1 r hr (by linarith only [hrR])
  have hd := coarse_fine_coordinate_distance (by positivity : 0 < 2*R) hη.le
    (show (η/4)*(2*R) ≤ η*R by nlinarith only [hη,hR])
    (fun x hx => by have hh := hUsub hx; change dist x p ≤ R at hh; linarith only [hh]) hc hf
  have hglobal := hX.splitting_coordinate_lipschitz hn (by positivity : 0 < 4*R) ht.le
    (by simpa only [show 8*(4*R)=2*(16*R) by ring] using hsplit)
  refine ⟨v,U,hU,hUsub,?_,LipschitzOnWith.of_dist_le_mul (fun x hx y hy => (hd x hx y hy).2),
    ?_,hc,hf⟩
  · have hsub : ball p R \ U ⊆ ball p (16*R) \ V := by
      intro x hx
      refine ⟨ball_subset_ball (by linarith only [hR]) hx.1,?_⟩
      intro hxV
      exact hx.2 ⟨hxV,ball_subset_closedBall hx.1⟩
    exact (measureReal_mono hsub (measure_ne_top_of_subset sdiff_subset
      (hX.finiteOnBounded _ isBounded_ball).ne)).trans hbad
  · apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    apply (hglobal.dist_le_mul x hx y hy).trans
    apply mul_le_mul_of_nonneg_right _ dist_nonneg
    change (n:ℝ)*(1+t) ≤ 2*n
    nlinarith [Nat.cast_nonneg (α := ℝ) n]

end RegularPointCoordinates

end

end OAI
