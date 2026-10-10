import OAI.Probability.ContinuumTransition.TailPressure

namespace OAI

section
open scoped Topology BigOperators
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

def ConstructionData.profile {p : ℝ} (C : ConstructionData p) : ℝ → ℝ :=
  physicalProfile C.t C.masses C.ranges

def ConstructionData.pressure {p : ℝ} (C : ConstructionData p) : Parameter → ℝ :=
  physicalPressure C.profile C.t

lemma ConstructionData.pressure_convex {p : ℝ} (C : ConstructionData p) :
    ConvexOn ℝ pressureDomain C.pressure :=
  physical_convex_bounded C.cap.t_large C.masses_nonneg C.ranges_one C.masses_summable (C.cap.weak C.mass_bound)

lemma ConstructionData.pressure_tendsto {p : ℝ} (C : ConstructionData p) {x : Parameter} (hx : x ∈ pressureDomain) :
    Tendsto (fun n => (C.stages n).pressure x) atTop (𝓝 (C.pressure x)) := by
  have hb (n : ℕ) := physical_pressure_tail_bound C.cap.t_large hx
    (prefixMass_nonneg C.masses_nonneg n) (tailMass_nonneg C.masses_nonneg n) C.ranges_one
    (prefixMass_summable C.masses_nonneg C.masses_summable n)
    (tailMass_summable C.masses_nonneg C.masses_summable n)
    (by rw [prefixMass_add_tailMass]; exact C.cap.small C.mass_bound) x.2
  have hb' (n : ℕ) : 0 ≤ C.pressure x-(C.stages n).pressure x ∧
      C.pressure x-(C.stages n).pressure x ≤
      108*2197*x.1*kernelHeight*momentConstant C.t x.1 (C.t*x.2)*(∑' k, tailMass C.masses n k) := by
    have hh := hb n
    rw [prefixMass_add_tailMass,← C.reference_eq_prefix n] at hh
    exact hh
  have hd : Tendsto (fun n => C.pressure x-(C.stages n).pressure x) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => (hb' n).1) (fun n => (hb' n).2)
    simpa only [mul_zero] using (tailMass_tsum_tendsto C.masses_nonneg C.masses_summable).const_mul
      (108*2197*x.1*kernelHeight*momentConstant C.t x.1 (C.t*x.2))
  simpa only [sub_sub_cancel,sub_zero] using (tendsto_const_nhds (x := C.pressure x)).sub hd

lemma initial_quarter_subset : ball initialPoint (1/4) ⊆ pressureDomain :=
  ball_subset_closedBall.trans ((closedBall_subset_closedBall (by norm_num : (1:ℝ)/4 ≤ 1/2)).trans
    (initial_ball_moderate.trans moderateBox_subset))

lemma ConstructionData.ideal_tendsto {p : ℝ} (C : ConstructionData p) {x : Parameter}
    (hx : x ∈ ball initialPoint (1/4)) :
    Tendsto (fun n => (C.stages n).ideal x) atTop (𝓝 (C.pressure x)) := by
  have hd : Tendsto (fun n => (C.stages n).ideal x-(C.stages (n+1)).pressure x) atTop (𝓝 0) := by
    apply squeeze_zero_norm _ geometricBudget_tendsto
    intro n
    simpa only [Real.norm_eq_abs,abs_sub_comm] using (C.transitions n).approximation x (ball_subset_closedBall hx)
  have hn := (C.pressure_tendsto (initial_quarter_subset hx)).comp (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def,sub_add_cancel,zero_add] using hd.add hn

lemma ConstructionData.ideal_locally_uniform {p : ℝ} (C : ConstructionData p) :
    TendstoLocallyUniformlyOn (fun n => (C.stages n).ideal) C.pressure atTop (ball initialPoint (1/4)) := by
  apply convex_pointwise_locally_uniform isOpen_ball
  · exact Eventually.of_forall (fun n => ((C.stages n).convex C.cap).subset initial_quarter_subset (convex_ball _ _))
  · exact fun _ hx => C.ideal_tendsto hx

lemma ConstructionData.limit_support_ball {p : ℝ} (C : ConstructionData p) (hp : 0 < p)
    {x : Parameter} (hx : Tendsto (fun n => (C.stages n).x) atTop (𝓝 x))
    (hnear : dist x initialPoint ≤ 1/8) :
    closedBall (triangleCenter p) C.γ ⊆ subgradients pressureDomain C.pressure x := by
  have hxW : x ∈ ball initialPoint (1/4) := hnear.trans_lt (by norm_num : (1:ℝ)/8 < 1/4)
  have hc := C.pressure_convex.continuousOn isOpen_pressureDomain
  have heval := C.ideal_locally_uniform.tendsto_comp (hc.mono initial_quarter_subset x hxW) hxW
    (tendsto_nhdsWithin_iff.mpr ⟨hx,Eventually.of_forall (fun n =>
      (C.stages n).x_near.trans (by norm_num : (1:ℝ)/8 < 1/4))⟩)
  intro v hv
  apply supportOn_of_local C.pressure_convex (initial_quarter_subset hxW)
  filter_upwards [isOpen_ball.mem_nhds hxW] with y hy
  have hd : Tendsto (fun n => pDot v (y-(C.stages n).x)) atTop (𝓝 (pDot v (y-x))) := by
    exact (show Continuous (fun z : Parameter => pDot v (y-z)) by unfold pDot; fun_prop).continuousAt.tendsto.comp hx
  apply le_of_tendsto_of_tendsto (heval.add hd) (C.ideal_tendsto hy)
  exact Eventually.of_forall (fun n =>
    ((C.stages n).triple.support_ball hp (groupRadius_le C.τ_pos.le n) C.τ_small C.geometry hv) y
      (initial_quarter_subset hy))

end ContinuumTemperature
end
end

end OAI
