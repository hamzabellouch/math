import OAI.Geometry.RCD.Coordinates.FirstOrderInnerCoordinates
import OAI.Geometry.RCD.Coordinates.RegularLargeGoodSets

namespace OAI

/-! # Actual fine coordinate maps on large regular-point good sets -/

open Set Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.regular_inner_good_coordinates {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n) (hK : K≤0)
    {p : X} (hp : IsRegular n p) {η ζ β : ℝ}
    (hη : 0<η) (hζ : 0<ζ) (hβ : 0<β) :
    ∃ t s : ℝ, 0<t ∧ t≤β ∧ 0<s ∧ ∀ R : ℝ, 0<R → R<s →
      ∃ (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
        (v : X → Euclidean n) (U : Set X),
        -1≤K*R^2 ∧ FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (2*R) t u v ∧
        IsCompact U ∧ U⊆closedBall p R ∧
        (hausdorff n X).real (ball p R \ U)≤ζ*(hausdorff n X).real (ball p R) ∧
        ∀ x∈U, ∀ r : ℝ, 0<r → r<R/2560 →
          IsPointedApproximation x 0 r (1/16) η (fun z => r⁻¹ • (v z-v x)) := by
  obtain ⟨r₀,ε,hr₀,hε,hcoord⟩ := hX.first_order_inner_coordinates hn hK
    (show 0<η/160 by positivity)
  let t := min ε β
  have ht : 0<t := lt_min hε hβ
  have htε : t≤ε := min_le_left _ _
  obtain ⟨s,hs,hgood⟩ := hX.regular_large_good_sets hn hp ht hζ
  let S := min s (min (16*r₀) (min 1 (1/(|K|+1))))
  have hS : 0<S := lt_min hs (lt_min (by positivity) (lt_min zero_lt_one (by positivity)))
  refine ⟨t,S,ht,min_le_right _ _,hS,?_⟩
  intro R hR hRS
  have hRs : R<s := hRS.trans_le (min_le_left _ _)
  have hRr : R≤16*r₀ := (hRS.le.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hR1 : R≤1 := ((hRS.le.trans (min_le_right _ _)).trans (min_le_right _ _)).trans
    (min_le_left _ _)
  have hRK : R≤1/(|K|+1) := ((hRS.le.trans (min_le_right _ _)).trans
    (min_le_right _ _)).trans (min_le_right _ _)
  have hcurv : -1≤K*R^2 := by
    have hmul := (le_div_iff₀ (by positivity : 0 < |K|+1)).mp hRK
    have hsq : R^2≤R := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hsq (abs_nonneg K)
    have hk := mul_le_mul_of_nonneg_right (neg_abs_le K) (sq_nonneg R)
    nlinarith
  obtain ⟨u,v,U,hsplit,hU,hUsub,hbad,hall⟩ := hgood R hR hRs
  refine ⟨u,v,U,hcurv,hsplit,hU,hUsub,hbad,?_⟩
  intro x hx r hr hrR
  have hlarge : 2560*r<R := by linarith
  have hcr : -1≤K*(16*(160*r))^2 := by
    have hh : (16*(160*r))^2≤R^2 := by nlinarith
    exact hcurv.trans (mul_le_mul_of_nonpos_left hh hK)
  have hsp : FirstOrderSplittingOn (hausdorff n X) hX.quadratic x (16*(160*r)) ε u v := by
    have hh := (hall x hx (2560*r) (by positivity) hlarge).mono_error _ _ ht.le htε
    simpa only [show (16:ℝ)*(160*r)=2560*r by ring] using hh
  have hh := hcoord x (160*r) (by positivity) (by linarith) hcr u v hsp
  have hout := hh.change_scale hr (by norm_num : (0:ℝ)<160)
  simpa only [show (160:ℝ)*(1/2560)=1/16 by norm_num,
    show (160:ℝ)*(η/160)=η by ring,smul_smul,
    show (160:ℝ)*(160*r)⁻¹=r⁻¹ by field_simp] using hout

end RegularPointCoordinates

end

end OAI
