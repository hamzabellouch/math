import OAI.Geometry.RCD.Coordinates.RegularLimitMidpointFamily

namespace OAI

/-! # Exact local quadratic midpoint geometry of the actual metric limits -/

open Set Filter Metric MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  [MetricSpace Y] [ProperSpace Y] {K : ℝ} {n : ℕ}
  (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]

include hX in
theorem regular_limit_quadratic_midpoint (hn : 2 ≤ n) (hK : K ≤ 0)
    {o : X} (ho : IsRegular n o) {q a b : Y}
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Y)
    (hp : Tendsto p atTop (𝓝 o)) (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (𝓝 0)) (hε : Tendsto ε atTop (𝓝 0))
    (hcurv : ∀ k, -1 ≤ K * (4 * r k)^2)
    (hV : ∀ k, IsPointedApproximation (p k) q (r k) 5 (ε k) (V k))
    (ha : dist a q < 1/2) (hb : dist b q < 1/2) :
    ∃ c : Y, dist c q < 1/2 ∧ dist a c = dist a b/2 ∧ dist c b = dist a b/2 ∧
      ∀ z ∈ ball q 1, dist z c^2 = (dist z a^2+dist z b^2)/2-dist a b^2/4 := by
  let W := ball q (1:ℝ)
  have hq : q ∈ W := by simp [W]
  let : Nonempty W := ⟨⟨q,hq⟩⟩
  obtain ⟨w,hw⟩ := TopologicalSpace.exists_dense_seq W
  obtain ⟨c,_hc,hac,hcb,hc⟩ := hX.regular_limit_midpoint_family hn hK ho
    (fun i => (w i : Y)) p r ε V hp hr hr0 hε hcurv hV ha hb (fun i => (w i).property)
  have hclosed : IsClosed {z : W | dist (z:Y) c^2 =
      (dist (z:Y) a^2+dist (z:Y) b^2)/2-dist a b^2/4} := by
    apply isClosed_eq
    · exact (continuous_subtype_val.dist continuous_const).pow 2
    · exact (((continuous_subtype_val.dist continuous_const).pow 2).add
        ((continuous_subtype_val.dist continuous_const).pow 2) |>.div_const 2).sub continuous_const
  have hall (z : W) : dist (z:Y) c^2 =
      (dist (z:Y) a^2+dist (z:Y) b^2)/2-dist a b^2/4 := by
    apply hclosed.closure_subset_iff.mpr _ (hw z)
    rintro _ ⟨i,rfl⟩
    exact hc i
  have hqc := hall ⟨q,hq⟩
  simp only [dist_comm q] at hqc
  have hsmall : dist c q < 1/2 := by
    nlinarith [dist_nonneg (x:=a) (y:=q),dist_nonneg (x:=b) (y:=q),
      dist_nonneg (x:=c) (y:=q),sq_nonneg (dist a b)]
  exact ⟨c,hsmall,hac,hcb,fun z hz => hall ⟨z,hz⟩⟩

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
