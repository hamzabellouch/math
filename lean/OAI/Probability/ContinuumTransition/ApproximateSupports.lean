import OAI.Probability.ContinuumTransition.ConstructionBounds

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma uniform_square_error_tendsto {F : Parameter → ℝ} {Q : ℕ → Parameter → ℝ}
    {a : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 0)) {x : Parameter} {r : ℝ}
    (happ : ∀ n, ∀ y ∈ ball x r, |Q n y-F y| ≤ (a n)^2)
    {Y : ℕ → Parameter} {y : Parameter} (hy : y ∈ ball x r)
    (hY : Tendsto Y atTop (𝓝 y)) (hF : ContinuousAt F y) :
    Tendsto (fun n => Q n (Y n)) atTop (𝓝 (F y)) := by
  have he : Tendsto (fun n => Q n (Y n)-F (Y n)) atTop (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    exact squeeze_zero' (Eventually.of_forall fun n => abs_nonneg (Q n (Y n)-F (Y n)))
      ((hY.eventually (isOpen_ball.mem_nhds hy)).mono fun n hn => happ n _ hn) (by simpa using ha.pow 2)
  have hh := he.add (hF.tendsto.comp hY)
  simpa only [Function.comp_def,sub_add_cancel,zero_add] using hh

lemma approximate_support_limit {F : Parameter → ℝ} (hF : ConvexOn ℝ pressureDomain F)
    {Q : ℕ → Parameter → ℝ} {a : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 0))
    {x : Parameter} (hx : x ∈ pressureDomain) {r : ℝ} (hr : 0 < r)
    (hball : ball x r ⊆ pressureDomain)
    (happ : ∀ n, ∀ y ∈ ball x r, |Q n y-F y| ≤ (a n)^2)
    {Y V : ℕ → Parameter} {v : Parameter}
    (hY : Tendsto Y atTop (𝓝 x)) (hV : Tendsto V atTop (𝓝 v))
    (hs : ∀ n, SupportOn pressureDomain (Q n) (Y n) (V n)) :
    SupportOn pressureDomain F x v := by
  apply supportOn_of_ball hF hx hr
  intro y hy
  have hcont := hF.continuousOn isOpen_pressureDomain
  have hqx := uniform_square_error_tendsto ha happ (mem_ball_self hr) hY
    (hcont.continuousAt (isOpen_pressureDomain.mem_nhds hx))
  have hqy := uniform_square_error_tendsto ha happ hy (tendsto_const_nhds (x := y))
    (hcont.continuousAt (isOpen_pressureDomain.mem_nhds (hball hy)))
  have hd : Tendsto (fun n => pDot (V n) (y-Y n)) atTop (𝓝 (pDot v (y-x))) := by
    exact (show Continuous (fun p : Parameter × Parameter => pDot p.1 (y-p.2)) by unfold pDot; fun_prop).tendsto
      (v,x) |>.comp (hV.prodMk_nhds hY)
  exact le_of_tendsto_of_tendsto (hqx.add hd) hqy (Eventually.of_forall fun n => hs n y (hball hy))

end ContinuumTemperature
end
end

end OAI
