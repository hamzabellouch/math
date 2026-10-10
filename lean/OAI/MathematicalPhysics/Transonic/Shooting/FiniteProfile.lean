import OAI.MathematicalPhysics.Transonic.Shooting.MatchedAxisJoin
import OAI.MathematicalPhysics.Transonic.Shooting.SonicGermEquation

namespace OAI

section
noncomputable section
namespace SepticProfile.SonicShooting
open Set Filter SourceFamily AxisBarriers
open scoped Topology ContDiff

def MatchedPair.localProfile (M : MatchedPair) : ℝ → ℝ :=
  ODEGlue.join (endRadius M.sonic.e) M.inner (M.sonic.germArc M.parameter)

lemma MatchedPair.arc_end (M : MatchedPair) :
    M.arc (endRadius M.sonic.e)=M.sonic.germArc M.parameter (endRadius M.sonic.e) := by
  have hb := (endRadius_bounds M.sonic.e_pos M.sonic.e_lt).1
  rw [MatchedPair.arc,ODEGlue.join,ite_eq_right (not_le.mpr hb),MatchedPair.eul,
    coord_end (by linarith [M.sonic.e_lt] : M.sonic.e<1),M.sonic.u_start]
  simp only [Family.germArc,endRadius,add_sub_cancel_left,UniformGerm.realFunction,UniformGerm.eulerFunction,Function.comp_apply]

lemma MatchedPair.inner_end (M : MatchedPair) :
    M.inner (endRadius M.sonic.e)=M.sonic.germArc M.parameter (endRadius M.sonic.e) := by
  have hb : M.axis.δ<endRadius M.sonic.e := by
    linarith [M.axis.δ_lt,(endRadius_bounds M.sonic.e_pos M.sonic.e_lt).1]
  simpa only [MatchedPair.inner,ODEGlue.join,ite_eq_right (not_le.mpr hb)] using M.arc_end

lemma MatchedPair.local_eventually_inner (M : MatchedPair) {z : ℝ}
    (hz : z<endRadius M.sonic.e) : M.localProfile =ᶠ[𝓝 z] M.inner := by
  filter_upwards [Iio_mem_nhds hz] with x hx
  exact ite_eq_left hx.le

lemma MatchedPair.local_eventually_germ (M : MatchedPair) {z : ℝ}
    (hz : endRadius M.sonic.e<z) : M.localProfile =ᶠ[𝓝 z] M.sonic.germArc M.parameter := by
  filter_upwards [Ioi_mem_nhds hz] with x hx
  exact ite_eq_right (not_le.mpr hx)

lemma MatchedPair.local_range (M : MatchedPair) {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) :
    M.localProfile z ∈ Ioo (0:ℝ) 1 := by
  unfold MatchedPair.localProfile ODEGlue.join
  split_ifs with h
  · exact M.inner_range ⟨hz.1,h⟩
  · exact M.sonic.germArc_below M.parameter ⟨le_of_not_ge h,hz.2⟩

lemma Family.germArc_derivative (F : Family) (p : Parameter) {z : ℝ}
    (hz : z ∈ Ico (endRadius F.e) 1) :
    HasDerivAt (F.germArc p) (N (kap p) z (F.germArc p z)/D (sig p) z (F.germArc p z)) z := by
  have hwd : |z-1|≤F.width := by
    rw [abs_of_neg (sub_neg.mpr hz.2)]
    unfold Family.width
    linarith [hz.1]
  have hr := hwd.trans_lt F.width_radius
  have hd := (F.germArc_analytic p hr).differentiableAt.hasDerivAt
  have hD : D (sig p) z (F.germArc p z)≠0 := ne_of_gt (normalized_D_pos (p:=p)
    ⟨by linarith [hz.1,(endRadius_bounds F.e_pos F.e_lt).1],hz.2.le⟩ (F.germArc_below p hz))
  have he := F.germArc_equation p hr
  apply hd.congr_deriv
  apply (eq_div_iff hD).mpr
  simpa only [mul_comm] using he

lemma MatchedPair.local_derivative_near_join (M : MatchedPair) {z : ℝ}
    (hz : z ∈ Icc (M.axis.δ/2) ((endRadius M.sonic.e+1)/2)) :
    HasDerivWithinAt M.localProfile
      (N (kap M.parameter) z (M.localProfile z)/D (sig M.parameter) z (M.localProfile z))
      (Icc (M.axis.δ/2) ((endRadius M.sonic.e+1)/2)) z := by
  have hr := endRadius_bounds M.sonic.e_pos M.sonic.e_lt
  apply ODEGlue.hasDerivWithinAt_join (f:=fun z u => N (kap M.parameter) z u/D (sig M.parameter) z u)
    (u:=M.inner) (v:=M.sonic.germArc M.parameter) (by linarith [M.axis.δ_lt]) (by linarith)
    (fun t ht => M.inner_derivative (by linarith [M.axis.δ_pos]) (by linarith [M.axis.δ_pos]) ht)
    (fun t ht => (M.sonic.germArc_derivative M.parameter ⟨ht.1,by linarith [ht.2]⟩).hasDerivWithinAt)
    M.inner_end z hz

lemma MatchedPair.local_smooth_at (M : MatchedPair) {z : ℝ}
    (hz : z ∈ Icc (0:ℝ) (1+M.sonic.width)) : ContDiffAt ℝ ∞ M.localProfile z := by
  rcases lt_trichotomy z (endRadius M.sonic.e) with hl | he | hr
  · exact (M.inner_smooth_at ⟨hz.1,hl⟩).congr_of_eventuallyEq (M.local_eventually_inner hl)
  · subst z
    have hrb := endRadius_bounds M.sonic.e_pos M.sonic.e_lt
    have ha : M.axis.δ/2<endRadius M.sonic.e := by linarith [M.axis.δ_lt]
    have hb : endRadius M.sonic.e<(endRadius M.sonic.e+1)/2 := by linarith
    have hf := ODEGlue.smooth_arc
      (f:=fun z u => N (kap M.parameter) z u/D (sig M.parameter) z u)
      (normalized_field_smooth M.parameter (by linarith [M.axis.δ_pos] : 0<M.axis.δ/2)
        (by linarith : (endRadius M.sonic.e+1)/2≤1))
      (fun t ht => M.local_derivative_near_join ht)
      (fun t ht => M.local_range ⟨by linarith [ht.1,M.axis.δ_pos],by linarith [ht.2]⟩)
    exact (hf _ ⟨ha.le,hb.le⟩).contDiffAt (Icc_mem_nhds ha hb)
  · have hwd : |z-1|≤M.sonic.width := by
      rw [abs_le]
      have hh := hz.2
      unfold Family.width at *
      constructor <;> linarith
    exact (M.sonic.germArc_analytic M.parameter (hwd.trans_lt M.sonic.width_radius)).contDiffAt.congr_of_eventuallyEq
      (M.local_eventually_germ hr)

lemma MatchedPair.local_equation (M : MatchedPair) {z : ℝ}
    (hz : z ∈ Icc (0:ℝ) (1+M.sonic.width)) :
    D (sig M.parameter) z (M.localProfile z)*deriv M.localProfile z=
      N (kap M.parameter) z (M.localProfile z) := by
  rcases lt_trichotomy z (endRadius M.sonic.e) with hl | he | hr
  · rw [(M.local_eventually_inner hl).eq_of_nhds,(M.local_eventually_inner hl).deriv_eq]
    exact M.inner_equation ⟨hz.1,hl⟩
  · subst z
    have hrb := endRadius_bounds M.sonic.e_pos M.sonic.e_lt
    have ha : M.axis.δ/2<endRadius M.sonic.e := by linarith [M.axis.δ_lt]
    have hb : endRadius M.sonic.e<(endRadius M.sonic.e+1)/2 := by linarith
    have hd := (M.local_derivative_near_join ⟨ha.le,hb.le⟩).hasDerivAt (Icc_mem_nhds ha hb)
    rw [hd.deriv]
    field_simp [ne_of_gt (normalized_D_pos (p:=M.parameter)
      ⟨by linarith,hrb.2.le⟩ (M.local_range ⟨by linarith,hrb.2⟩))]
  · rw [(M.local_eventually_germ hr).eq_of_nhds,(M.local_eventually_germ hr).deriv_eq]
    apply M.sonic.germArc_equation
    apply lt_of_le_of_lt _ M.sonic.width_radius
    rw [abs_le]
    have hh := hz.2
    unfold Family.width at *
    constructor <;> linarith

lemma MatchedPair.local_value (M : MatchedPair) : M.localProfile 1=1 := by
  rw [(M.local_eventually_germ (endRadius_bounds M.sonic.e_pos M.sonic.e_lt).2).eq_of_nhds]
  exact M.sonic.germArc_value M.parameter

lemma MatchedPair.local_slope (M : MatchedPair) : 0<deriv M.localProfile 1 := by
  rw [(M.local_eventually_germ (endRadius_bounds M.sonic.e_pos M.sonic.e_lt).2).deriv_eq,
    M.sonic.germArc_slope]
  exact ShootingParameters.slope_pos M.parameter.property

lemma MatchedPair.local_unique_sonic (M : MatchedPair) {z : ℝ}
    (hz : z ∈ Ioc (0:ℝ) (1+M.sonic.width)) : M.localProfile z=1 ↔ z=1 := by
  constructor
  · intro he
    rcases lt_trichotomy z 1 with hl | heq | hr
    · exact False.elim (ne_of_lt (M.local_range ⟨hz.1,hl⟩).2 he)
    · exact heq
    · have heq := (M.local_eventually_germ ((endRadius_bounds M.sonic.e_pos M.sonic.e_lt).2.trans hr)).eq_of_nhds
      have hg := M.sonic.germArc_above M.parameter ⟨hr,hz.2⟩
      rw [← heq,he] at hg
      exact False.elim (lt_irrefl _ hg)
  · rintro rfl
    exact M.local_value

end SepticProfile.SonicShooting

end
end

end OAI
