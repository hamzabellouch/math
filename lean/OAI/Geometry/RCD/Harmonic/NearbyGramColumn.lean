import OAI.Geometry.RCD.Harmonic.FirstOrderColumnEndpoint
import OAI.Geometry.RCD.Harmonic.FirstOrderGramDefectLimit
import OAI.Geometry.RCD.Harmonic.AffineSpatialSelection

namespace OAI

/-! # Nearby paths with vanishing Gram error and a prescribed column bound -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal InnerProductSpace
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.nearby_gram_column {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n) (hK : K≤0)
    (p x y : ℕ → X) (r ε : ℕ → ℝ) (hr : ∀ k, 0<r k) (hr0 : Tendsto r atTop (𝓝 0))
    (hcurv : ∀ k, -1≤K*(16*r k)^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hε0 : Tendsto ε atTop (𝓝 0))
    (u : ℕ → Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (v : ℕ → X → Euclidean n)
    (hsplit : ∀ k, FirstOrderSplittingOn (hausdorff n X) hX.quadratic
      (p k) (16*r k) (ε k) (u k) (v k))
    (hx : ∀ k, dist (x k) (p k)≤r k/48) (hy : ∀ k, dist (y k) (p k)≤r k/48)
    (a : ℕ → Euclidean n) :
    ∃ (δ e : ℕ → ℝ) (γ : ℕ → C(Time,X)),
      (∀ k, 0<δ k ∧ δ k≤1/2) ∧ Tendsto δ atTop (𝓝 0) ∧
      (∀ k, 0≤e k) ∧ Tendsto e atTop (𝓝 0) ∧
      (∀ k, dist (γ k 0) (x k)<δ k*r k/24 ∧ dist (γ k 1) (y k)<δ k*r k/24 ∧
        ∀ t : Time, dist (γ k t) (p k)≤r k/8) ∧
      ∀ k, ⟪v k (γ k 1)-v k (γ k 0),a k⟫_ℝ^2≤
        (dist (γ k 0) (γ k 1))^2*‖a k‖^2*(1+e k) := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  let E k := gramDefect μ Q (u k)
  have hEI (k : ℕ) : IntegrableOn (E k) (ball (p k) (4*r k)) μ :=
    gramDefect_integrableOn μ Q (u k) (hX.finiteOnBounded _ isBounded_ball).ne
  have hE0 := hX.first_order_gram_defect_limit hn p r ε hr hcurv hε hε0 u v hsplit
  obtain ⟨δ,π,F,hδ,hδ0,hπ,hgeo,hopt,hcomp,hends,hFeq,hinner,hI,hlim⟩ :=
    hX.first_order_nearby_plan_errors hn hK p x y r ε hr hr0 hcurv hε hε1 hε0
      u v hsplit hx hy E (fun k => gramDefect_nonneg μ Q (u k)) hEI hE0
  let (k : ℕ) : IsProbabilityMeasure (π k) := hπ k
  have hstart (k : ℕ) : ∀ᵐ z ∂(π k).map (fun γ => γ 0), dist z (p k)≤r k/12 := by
    apply (ae_map_iff (measurable_path_eval 0).aemeasurable isClosed_closedBall.measurableSet).mpr
    filter_upwards [hends k] with γ he
    have hh := dist_triangle (γ 0) (x k) (p k)
    nlinarith [hx k,(hδ k).2,hr k]
  have hfinish (k : ℕ) : ∀ᵐ z ∂(π k).map (fun γ => γ 1), dist z (p k)≤r k/12 := by
    apply (ae_map_iff (measurable_path_eval 1).aemeasurable isClosed_closedBall.measurableSet).mpr
    filter_upwards [hends k] with γ he
    have hh := dist_triangle (γ 1) (y k) (p k)
    nlinarith [hy k,(hδ k).2,hr k]
  have hcol (k : ℕ) : ∀ᵐ γ ∂π k,
      ⟪v k (γ 1)-v k (γ 0),a k⟫_ℝ^2≤(dist (γ 0) (γ 1))^2*‖a k‖^2*
        (1+∫ t in Icc (0:ℝ) 1, E k (geodesicExtension γ t)) := by
    obtain ⟨C,hC,hc⟩ := hcomp k
    exact hX.first_order_column_endpoint hn (hr k) (hε k) (hε1 k) (u k) (v k) (hsplit k)
      (a k) (π k) (hgeo k) (hopt k) hC hc (hstart k) (hfinish k)
  let P k γ :=
    (dist (γ 0) (x k)<δ k*r k/24 ∧ dist (γ 1) (y k)<δ k*r k/24 ∧
      ∀ t : Time, dist (γ t) (p k)≤r k/8) ∧
    (∀ i (t : Time), F k i γ t=
      (v k (γ t) i-((1-(t:ℝ))*v k (γ 0) i+(t:ℝ)*v k (γ 1) i))/r k) ∧
    ⟪v k (γ 1)-v k (γ 0),a k⟫_ℝ^2≤(dist (γ 0) (γ 1))^2*‖a k‖^2*
      (1+∫ t in Icc (0:ℝ) 1, E k (geodesicExtension γ t))
  have hP (k : ℕ) : ∀ᵐ γ ∂π k, P k γ := (hends k).and ((hFeq k).and (hcol k))
  obtain ⟨γ,e,hPγ,he,he0,_haff,hEγ⟩ := affine_spatial_selection π F E
    (fun k => gramDefect_nonneg μ Q (u k)) hI hlim P hP
  refine ⟨δ,e,γ,hδ,hδ0,he,he0,fun k => (hPγ k).1,?_⟩
  intro k
  exact ((hPγ k).2.2).trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl (hEγ k))
    (mul_nonneg (sq_nonneg _) (sq_nonneg _)))

end RegularPointCoordinates

end

end OAI
