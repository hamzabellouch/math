import OAI.Geometry.RCD.Harmonic.FirstOrderIsometricCompactness
import OAI.Geometry.RCD.Harmonic.FirstOrderLimitNoSupport
import OAI.Geometry.RCD.Metric.MetricLimitConvexImage
import OAI.Geometry.RCD.Metric.MetricLimitBallImage

namespace OAI

/-! # The actual first-order coordinates fill a Euclidean ball in the metric limit -/

open Set Filter Metric MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
universe u
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.first_order_euclidean_limit {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n) (hK : K≤0)
    (p : ℕ → X) (r ε : ℕ → ℝ)
    (hr : ∀ k, 0<r k) (hr0 : Tendsto r atTop (𝓝 0))
    (hcurv : ∀ k, -1≤K*(80*r k)^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hε0 : Tendsto ε atTop (𝓝 0))
    (U : ℕ → Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (v : ℕ → X → Euclidean n)
    (hsplit : ∀ k, FirstOrderSplittingOn (hausdorff n X) hX.quadratic
      (p k) (80*r k) (ε k) (U k) (v k)) :
    ∃ a : ℕ → ℕ, StrictMono a ∧ ∃ (Y : Type u) (dY : MetricSpace Y),
      let := dY
      ∃ (_ : ProperSpace Y) (q : Y) (δ : ℕ → ℝ) (V : ℕ → X → Y) (F : Y → Euclidean n),
        (∀ k, 0<δ k ∧ δ k≤1) ∧ Tendsto δ atTop (𝓝 0) ∧
        (∀ k, IsPointedApproximation (p (a k)) q (r (a k)) 5 (δ k) (V k)) ∧
        Continuous F ∧ F q=0 ∧
        (∀ η : ℝ, 0<η → ∀ᶠ k in atTop, ∀ x, dist x (p (a k))≤5*r (a k) →
          dist ((r (a k))⁻¹ • (v (a k) x-v (a k) (p (a k)))) (F (V k x))≤η) ∧
        (∀ y z, dist y q<1/16 → dist z q<1/16 → dist (F y) (F z)=dist y z) ∧
        F '' closedBall q (1/256)=closedBall 0 (1/256) := by
  obtain ⟨a,ha,Y,dY,hproper,q,δ,V,g,hδ,hδ0,hV,hg,hvalues,hiso⟩ :=
    hX.first_order_isometric_compactness hn hK p r ε hr hr0 hcurv hε hε1 hε0 U v hsplit
  let := dY
  let := hproper
  let F : Y → Euclidean n := fun y => WithLp.toLp 2 (fun i => g i y)
  have hF : Continuous F := (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp
    (continuous_pi (fun i => (hg i).1.continuous))
  have hFq : F q=0 := by
    ext i
    exact (hg i).2
  have hv := finite_metric_value_limit (p∘a) (r∘a) V
    (fun k x => (r (a k))⁻¹ • (v (a k) x-v (a k) (p (a k)))) g
    (fun i η hη => by
      simpa only [Function.comp_apply,PiLp.smul_apply,PiLp.sub_apply,smul_eq_mul,div_eq_inv_mul]
        using hvalues i η hη)
  refine ⟨a,ha,Y,dY,hproper,q,δ,V,F,hδ,hδ0,hV,hF,hFq,hv,hiso,?_⟩
  obtain ⟨hc,hconv⟩ := metric_limit_convex_image hX.geodesic (p∘a) (r∘a) δ V
    (fun k => hr (a k)) hδ0 hV F hF hiso
  have himage := metric_limit_closedBall_image F q hc hconv hiso (by
    intro y hy b hb hs
    exact hX.first_order_limit_no_support hn hK (p∘a) (r∘a) (ε∘a) δ V q
      (fun k => hr (a k)) (hr0.comp ha.tendsto_atTop) (fun k => hcurv (a k))
      (fun k => hε (a k)) (fun k => hε1 (a k)) (hε0.comp ha.tendsto_atTop)
      hδ0 hV (U∘a) (v∘a) (fun k => hsplit (a k)) F hF hv hy b hb hs)
  simpa only [hFq] using himage

end RegularPointCoordinates

end

end OAI
