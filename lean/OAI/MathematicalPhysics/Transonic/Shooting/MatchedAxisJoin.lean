import OAI.MathematicalPhysics.Transonic.Shooting.MatchedInterior
import OAI.MathematicalPhysics.Transonic.Shooting.AxisGermEquation

namespace OAI

section
noncomputable section
namespace SepticProfile.SonicShooting
open Set Filter SourceFamily AxisBarriers
open scoped Topology ContDiff

def MatchedPair.axisGerm (M : MatchedPair) : ℝ → ℝ := M.axis.germ.velocity M.parameter

def MatchedPair.inner (M : MatchedPair) : ℝ → ℝ := ODEGlue.join M.axis.δ M.axisGerm M.arc

lemma MatchedPair.axisGerm_analytic (M : MatchedPair) {z : ℝ}
    (hz : z ∈ Icc (0:ℝ) M.axis.δ) : AnalyticAt ℝ M.axisGerm z := by
  apply M.axis.germ.velocity_analytic
  have hsq : z^2≤M.axis.δ^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hz.2) (add_nonneg M.axis.δ_pos.le hz.1)]
  exact hsq.trans_lt M.axis.δ_radius

lemma MatchedPair.axisGerm_range (M : MatchedPair) {z : ℝ}
    (hz : z ∈ Ioc (0:ℝ) M.axis.δ) : M.axisGerm z ∈ Ioo (0:ℝ) 1 := by
  have hh := M.axis.germ_range M.parameter z hz
  have hp : 0<(749/1000:ℝ)*z := mul_pos (by norm_num) hz.1
  change 0<z*(M.axis.germ.G M.parameter ((z^2:ℝ):ℂ)).re ∧
    z*(M.axis.germ.G M.parameter ((z^2:ℝ):ℂ)).re<1
  constructor <;> linarith [hh.1,hh.2,hz.2,M.axis.δ_lt]

lemma MatchedPair.axisGerm_equation (M : MatchedPair) {z : ℝ}
    (hz : z ∈ Icc (0:ℝ) M.axis.δ) :
    D (sig M.parameter) z (M.axisGerm z)*deriv M.axisGerm z=N (kap M.parameter) z (M.axisGerm z) := by
  apply M.axis.germ.velocity_equation
  have hsq : z^2≤M.axis.δ^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hz.2) (add_nonneg M.axis.δ_pos.le hz.1)]
  exact hsq.trans_lt M.axis.δ_radius

lemma MatchedPair.axisGerm_derivative (M : MatchedPair) {z : ℝ}
    (hz : z ∈ Ioc (0:ℝ) M.axis.δ) :
    HasDerivAt M.axisGerm (N (kap M.parameter) z (M.axisGerm z)/D (sig M.parameter) z (M.axisGerm z)) z := by
  have hd := (M.axisGerm_analytic ⟨hz.1.le,hz.2⟩).differentiableAt.hasDerivAt
  have hD := ne_of_gt (normalized_D_pos (p:=M.parameter)
    ⟨hz.1,by linarith [hz.2,M.axis.δ_lt]⟩ (M.axisGerm_range hz))
  have he := M.axisGerm_equation ⟨hz.1.le,hz.2⟩
  have hv : deriv M.axisGerm z=N (kap M.parameter) z (M.axisGerm z)/D (sig M.parameter) z (M.axisGerm z) := by
    apply (eq_div_iff hD).mpr
    simpa only [mul_comm] using he
  rwa [hv] at hd

lemma MatchedPair.arc_start (M : MatchedPair) : M.arc M.axis.δ=M.axisGerm M.axis.δ := by
  have h1 : M.axis.δ≤(99/100:ℝ) := by linarith [M.axis.δ_lt]
  have h2 : M.axis.δ≤(9/10:ℝ) := by linarith [M.axis.δ_lt]
  simp only [MatchedPair.arc,MatchedPair.middle,ODEGlue.join,ite_eq_left h1,ite_eq_left h2,
    M.axis.start,MatchedPair.axisGerm,AxisFamily.UniformGerm.velocity,AxisFamily.UniformGerm.realFunction]

lemma MatchedPair.inner_range (M : MatchedPair) {z : ℝ}
    (hz : z ∈ Ioc (0:ℝ) (endRadius M.sonic.e)) : M.inner z ∈ Ioo (0:ℝ) 1 := by
  unfold MatchedPair.inner ODEGlue.join
  split_ifs with h
  · exact M.axisGerm_range ⟨hz.1,h⟩
  · exact M.arc_range ⟨le_of_not_ge h,hz.2⟩

lemma MatchedPair.inner_derivative (M : MatchedPair) {a z : ℝ}
    (ha : 0<a) (had : a≤M.axis.δ) (hz : z ∈ Icc a (endRadius M.sonic.e)) :
    HasDerivWithinAt M.inner (N (kap M.parameter) z (M.inner z)/D (sig M.parameter) z (M.inner z))
      (Icc a (endRadius M.sonic.e)) z := by
  apply ODEGlue.hasDerivWithinAt_join (f:=fun z u => N (kap M.parameter) z u/D (sig M.parameter) z u)
    (u:=M.axisGerm) (v:=M.arc) had (by linarith [M.axis.δ_lt,(endRadius_bounds M.sonic.e_pos M.sonic.e_lt).1])
    (fun t ht => (M.axisGerm_derivative ⟨ha.trans_le ht.1,ht.2⟩).hasDerivWithinAt)
    (fun t ht => M.arc_derivative ht) M.arc_start.symm z hz

lemma MatchedPair.inner_smooth_between (M : MatchedPair) {a : ℝ} (ha : 0<a) (had : a≤M.axis.δ) :
    ContDiffOn ℝ ∞ M.inner (Icc a (endRadius M.sonic.e)) :=
  ODEGlue.smooth_arc (f:=fun z u => N (kap M.parameter) z u/D (sig M.parameter) z u)
    (normalized_field_smooth M.parameter ha (endRadius_bounds M.sonic.e_pos M.sonic.e_lt).2.le)
    (fun _ hz => M.inner_derivative ha had hz)
    (fun _ hz => M.inner_range ⟨ha.trans_le hz.1,hz.2⟩)

lemma MatchedPair.inner_eventually_axis (M : MatchedPair) {z : ℝ} (hz : z<M.axis.δ) :
    M.inner =ᶠ[𝓝 z] M.axisGerm := by
  filter_upwards [Iio_mem_nhds hz] with x hx
  exact ite_eq_left hx.le

lemma MatchedPair.inner_smooth_at (M : MatchedPair) {z : ℝ}
    (hz : z ∈ Ico (0:ℝ) (endRadius M.sonic.e)) : ContDiffAt ℝ ∞ M.inner z := by
  by_cases hd : z<M.axis.δ
  · exact (M.axisGerm_analytic ⟨hz.1,hd.le⟩).contDiffAt.congr_of_eventuallyEq (M.inner_eventually_axis hd)
  · have hd' : M.axis.δ≤z := le_of_not_gt hd
    have ha : M.axis.δ/2<z := by linarith [M.axis.δ_pos]
    exact (M.inner_smooth_between (by linarith [M.axis.δ_pos] : 0<M.axis.δ/2)
      (by linarith [M.axis.δ_pos]) z ⟨ha.le,hz.2.le⟩).contDiffAt (Icc_mem_nhds ha hz.2)

lemma MatchedPair.inner_equation (M : MatchedPair) {z : ℝ}
    (hz : z ∈ Ico (0:ℝ) (endRadius M.sonic.e)) :
    D (sig M.parameter) z (M.inner z)*deriv M.inner z=N (kap M.parameter) z (M.inner z) := by
  by_cases hd : z<M.axis.δ
  · have he := M.axisGerm_equation ⟨hz.1,hd.le⟩
    rw [(M.inner_eventually_axis hd).eq_of_nhds,(M.inner_eventually_axis hd).deriv_eq]
    exact he
  · have hd' : M.axis.δ≤z := le_of_not_gt hd
    have ha : M.axis.δ/2<z := by linarith [M.axis.δ_pos]
    have hz0 : 0<z := M.axis.δ_pos.trans_le hd'
    have hder := (M.inner_derivative (by linarith [M.axis.δ_pos] : 0<M.axis.δ/2)
      (by linarith [M.axis.δ_pos]) ⟨ha.le,hz.2.le⟩).hasDerivAt (Icc_mem_nhds ha hz.2)
    rw [hder.deriv]
    field_simp [ne_of_gt (normalized_D_pos (p:=M.parameter)
      ⟨hz0,hz.2.le.trans (endRadius_bounds M.sonic.e_pos M.sonic.e_lt).2.le⟩
      (M.inner_range ⟨hz0,hz.2.le⟩))]

end SepticProfile.SonicShooting

end
end

end OAI
