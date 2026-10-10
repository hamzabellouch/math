import OAI.Geometry.RCD.Coordinates.RegularInnerGoodCoordinates
import OAI.Geometry.RCD.Coordinates.CoarseFineCoordinateDistance
import OAI.Geometry.RCD.Coordinates.SplittingCoordinateLipschitz
import OAI.Geometry.RCD.Metric.ApproximationRestriction

namespace OAI

/-! # Coarse and fine image data without the published product premise -/

open Set Metric MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.regular_actual_image_good_sets {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n) (hK : K≤0)
    {p : X} (hp : IsRegular n p) {η ζ : ℝ} (hη : 0<η) (hζ : 0<ζ) :
    ∃ s : ℝ, 0<s ∧ ∀ R : ℝ, 0<R → R<s → -1≤K*(163840*R)^2 →
      ∃ (v : X → Euclidean n) (U : Set X),
        IsCompact U ∧ U⊆closedBall p R ∧
        (hausdorff n X).real (ball p R \ U)≤ζ*(hausdorff n X).real (ball p (16*R)) ∧
        LipschitzOnWith ⟨1+32*η,by positivity⟩ v U ∧
        LipschitzOnWith ⟨2*(n:ℝ),by positivity⟩ v (ball p (4*R)) ∧
        IsPointedApproximation p 0 (2*R) (1/2) (η/4)
          (fun x => (2*R)⁻¹ • (v x-v p)) ∧
        ∀ x∈U, ∀ r : ℝ, 0<r → r<R →
          IsPointedApproximation x 0 r (1/16) η (fun z => r⁻¹ • (v z-v x)) := by
  obtain ⟨D,hD,hvol⟩ := hX.rescaled_ball_volume_factor hn
    (a:=1) (δ:=1/5120) (by norm_num) (by norm_num) (by norm_num)
  have hD0 : 0<D := lt_of_lt_of_le zero_lt_one hD
  obtain ⟨d,ε,hd,hε,hcoarse⟩ := hX.first_order_small_scale_approximation hn hK
    (show 0<η/12 by positivity)
  obtain ⟨t,s,ht,htsmall,hs,hsets⟩ := hX.regular_inner_good_coordinates hn hK hp hη
    (show 0<ζ/D by positivity) (lt_min hε zero_lt_one)
  have htε : t≤ε := htsmall.trans (min_le_left _ _)
  have ht1 : t≤1 := htsmall.trans (min_le_right _ _)
  refine ⟨min (s/81920) (d/2),lt_min (by positivity) (by positivity),?_⟩
  intro R hR hRs hcurv
  have hbigR : 0<81920*R := by positivity
  obtain ⟨u,v,V,_hc,hsplit,hV,hVsub,hbad,hfine⟩ := hsets (81920*R) hbigR
    (by linarith [hRs.trans_le (min_le_left _ _)])
  let U := V∩closedBall p R
  have hU : IsCompact U := hV.inter_right isClosed_closedBall
  have hUsub : U⊆closedBall p R := inter_subset_right
  have hc : IsPointedApproximation p 0 (2*R) (1/2) (η/4)
      (fun x => (2*R)⁻¹ • (v x-v p)) := by
    have hsp : FirstOrderSplittingOn (hausdorff n X) hX.quadratic
        p (81920*(2*R)) ε u v := by
      simpa only [show 2*(81920*R)=81920*(2*R) by ring] using
        hsplit.mono_error _ _ ht.le htε
    have hh := hcoarse p (2*R) (by positivity)
      (by linarith [hRs.trans_le (min_le_right _ _)])
      (by simpa only [show 81920*(2*R)=163840*R by ring] using hcurv) u v hsp
    simpa only [show 3*(η/12)=η/4 by ring] using
      hh.restrict_radius (by positivity) (by norm_num : (0:ℝ)≤1/2)
        (by norm_num : (1/2:ℝ)≤2) (by positivity : 0≤η/12)
  have hf : ∀ x∈U, ∀ r : ℝ, 0<r → r<R →
      IsPointedApproximation x 0 r (1/16) η (fun z => r⁻¹ • (v z-v x)) := by
    intro x hx r hr hrR
    exact hfine x hx.1 r hr (by linarith)
  have hg := hX.splitting_coordinate_lipschitz hn
    (show 0<(81920*R)/4 by positivity) ht.le
    (by simpa only [show 8*((81920*R)/4)=2*(81920*R) by ring] using hsplit)
  have hdistance := coarse_fine_coordinate_distance (show 0<2*R by positivity) hη.le
    (show (η/4)*(2*R)≤η*R by nlinarith)
    (fun x hx => by have hh := hUsub hx; change dist x p≤R at hh; linarith) hc hf
  refine ⟨v,U,hU,hUsub,?_,LipschitzOnWith.of_dist_le_mul
    (fun x hx y hy => (hdistance x hx y hy).2),?_,hc,hf⟩
  · have hsub : ball p R \ U⊆ball p (81920*R) \ V := by
      intro x hx
      refine ⟨ball_subset_ball (by linarith) hx.1,?_⟩
      intro hxV
      exact hx.2 ⟨hxV,ball_subset_closedBall hx.1⟩
    have hcBig : -1≤K*(81920*R)^2 := by
      have he : K*(163840*R)^2=4*(K*(81920*R)^2) := by ring
      rw [he] at hcurv
      nlinarith
    have hmass := hvol p (81920*R) hbigR hcBig p (by simp; positivity)
    have he : (1/5120:ℝ)*(81920*R)=16*R := by ring
    rw [he] at hmass
    calc
      _≤(hausdorff n X).real (ball p (81920*R) \ V) :=
        measureReal_mono hsub (measure_ne_top_of_subset sdiff_subset
          (hX.finiteOnBounded _ isBounded_ball).ne)
      _≤(ζ/D)*(hausdorff n X).real (ball p (81920*R)) := hbad
      _≤(ζ/D)*(D*(hausdorff n X).real (ball p (16*R))) :=
        mul_le_mul_of_nonneg_left hmass (by positivity)
      _=ζ*(hausdorff n X).real (ball p (16*R)) := by field_simp
  · apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hx' : x∈ball p ((81920*R)/4) := ball_subset_ball (by linarith) hx
    have hy' : y∈ball p ((81920*R)/4) := ball_subset_ball (by linarith) hy
    apply (hg.dist_le_mul x hx' y hy').trans
    apply mul_le_mul_of_nonneg_right _ dist_nonneg
    change (n:ℝ)*(1+t)≤2*n
    nlinarith [Nat.cast_nonneg (α:=ℝ) n]

end RegularPointCoordinates

end

end OAI
