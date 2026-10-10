import OAI.MathematicalPhysics.Transonic.Shooting.EulerCoordinates
import OAI.MathematicalPhysics.Transonic.Shooting.ODEGlue

namespace OAI

section
noncomputable section

namespace SepticProfile.SonicShooting
open Set SourceFamily AxisBarriers
open scoped ContDiff

def MatchedPair.reg (M : MatchedPair) (z : ℝ) : ℝ := M.sonic.v M.parameter (99/100-z)
def MatchedPair.eul (M : MatchedPair) (z : ℝ) : ℝ := M.sonic.u M.parameter (coord z)
def MatchedPair.middle (M : MatchedPair) : ℝ → ℝ :=
  ODEGlue.join (9/10) (M.axis.u M.parameter) M.reg
def MatchedPair.arc (M : MatchedPair) : ℝ → ℝ :=
  ODEGlue.join (99/100) M.middle M.eul

lemma normalized_D_pos {p : Parameter} {z u : ℝ} (hz : z ∈ Ioc (0:ℝ) 1)
    (hu : u ∈ Ioo (0:ℝ) 1) : 0<D (sig p) z u := by
  have hs := ShootingParameters.sigma_bounds p.property
  exact ShootingField.D_positive hs.1.le hs.2 hz hu.2 ⟨hu.1.le,le_rfl⟩

lemma normalized_field_smooth (p : Parameter) {a b : ℝ} (ha : 0<a) (hb : b≤1) :
    ContDiffOn ℝ ∞ (fun q : ℝ×ℝ => N (kap p) q.1 q.2/D (sig p) q.1 q.2)
      (Icc a b ×ˢ Ioo 0 1) := by
  apply ContDiffOn.div
  · unfold N; fun_prop
  · unfold D; fun_prop
  · intro q hq
    exact ne_of_gt (normalized_D_pos ⟨ha.trans_le hq.1.1,hq.1.2.trans hb⟩ hq.2)

lemma MatchedPair.reg_range (M : MatchedPair) {z : ℝ} (hz : z ∈ Icc (9/10:ℝ) (99/100)) :
    M.reg z ∈ Ioo (0:ℝ) 1 := by
  have hh := M.regular_equation.1 (99/100-z) ⟨by linarith [hz.2],by linarith [hz.1]⟩
  exact ⟨hh.1,hh.2.trans (by norm_num)⟩

lemma MatchedPair.eul_range (M : MatchedPair) {z : ℝ}
    (hz : z ∈ Icc (99/100:ℝ) (endRadius M.sonic.e)) : M.eul z ∈ Ioo (0:ℝ) 1 := by
  have hh := M.euler_equation.1 (coord z) (coord_range M.sonic.e_pos M.sonic.e_lt hz)
  exact ⟨hh.1,hh.2.trans (by linarith [M.sonic.e_pos])⟩

lemma MatchedPair.reg_derivative (M : MatchedPair) {z : ℝ} (hz : z ∈ Icc (9/10:ℝ) (99/100)) :
    HasDerivWithinAt M.reg (N (kap M.parameter) z (M.reg z)/D (sig M.parameter) z (M.reg z))
      (Icc (9/10) (99/100)) z := by
  have hm : MapsTo (fun z:ℝ => 99/100-z) (Icc (9/10) (99/100)) (Icc 0 (9/100)) :=
    fun x hx => ⟨by linarith [hx.2],by linarith [hx.1]⟩
  have hd := (M.regular_equation.2 _ (hm hz)).comp (h:=fun x:ℝ => 99/100-x) z
    (((hasDerivAt_const z (99/100)).sub (hasDerivAt_id z)).hasDerivWithinAt) hm
  have heq : (-IntegerPolynomial.numer (kap M.parameter) (99/100-(99/100-z)) (M.reg z)/
      IntegerPolynomial.denom (sig M.parameter) (99/100-(99/100-z)) (M.reg z))*(0-1) =
      N (kap M.parameter) z (M.reg z)/D (sig M.parameter) z (M.reg z) := by
    simp only [sub_sub_cancel,zero_sub,neg_div,neg_mul]
    unfold N D IntegerPolynomial.numer IntegerPolynomial.denom
    ring
  change HasDerivWithinAt M.reg _ _ _ at hd
  exact hd.congr_deriv heq

lemma MatchedPair.eul_derivative (M : MatchedPair) {z : ℝ}
    (hz : z ∈ Icc (99/100:ℝ) (endRadius M.sonic.e)) :
    HasDerivWithinAt M.eul (N (kap M.parameter) z (M.eul z)/D (sig M.parameter) z (M.eul z))
      (Icc (99/100) (endRadius M.sonic.e)) z := by
  have hzl : z<1 := hz.2.trans_lt (endRadius_bounds M.sonic.e_pos M.sonic.e_lt).2
  have hm : MapsTo coord (Icc (99/100:ℝ) (endRadius M.sonic.e)) (Icc M.sonic.e (5/6)) :=
    fun x hx => coord_range M.sonic.e_pos M.sonic.e_lt hx
  have hd := (M.euler_equation.2 _ (hm hz)).comp (h:=coord) z
    (coord_derivative hzl).hasDerivWithinAt hm
  change HasDerivWithinAt M.eul _ _ _ at hd
  exact hd.congr_deriv (coord_field (sig M.parameter) (kap M.parameter) z (M.eul z) hzl (ne_of_gt (normalized_D_pos (p:=M.parameter)
    ⟨by linarith [hz.1],hzl.le⟩ (M.eul_range hz))))

lemma MatchedPair.axis_range (M : MatchedPair) {z : ℝ}
    (hz : z ∈ Icc M.axis.δ (9/10)) : M.axis.u M.parameter z ∈ Ioo (0:ℝ) 1 := by
  have hr := M.axis.range M.parameter z hz
  have hzp : 0<z := M.axis.δ_pos.trans_le hz.1
  refine ⟨lt_of_lt_of_le ?_ hr.1, hr.2.trans_lt (barriers_in_unit ⟨hzp.le,hz.2⟩).2.2.2⟩
  unfold lower; positivity

lemma MatchedPair.middle_derivative (M : MatchedPair) {z : ℝ}
    (hz : z ∈ Icc M.axis.δ (99/100)) :
    HasDerivWithinAt M.middle (N (kap M.parameter) z (M.middle z)/D (sig M.parameter) z (M.middle z))
      (Icc M.axis.δ (99/100)) z := by
  apply ODEGlue.hasDerivWithinAt_join (f:=fun z u => N (kap M.parameter) z u/D (sig M.parameter) z u)
    (u:=M.axis.u M.parameter) (v:=M.reg) (by linarith [M.axis.δ_lt]) (by norm_num)
    (M.axis.derivative M.parameter) (fun t ht => M.reg_derivative ht) _ z hz
  simpa only [MatchedPair.reg,show (99/100:ℝ)-9/10=9/100 by norm_num] using M.match_eq.symm

lemma MatchedPair.middle_range (M : MatchedPair) {z : ℝ}
    (hz : z ∈ Icc M.axis.δ (99/100)) : M.middle z ∈ Ioo (0:ℝ) 1 := by
  unfold MatchedPair.middle ODEGlue.join
  split_ifs with h
  · exact M.axis_range ⟨hz.1,h⟩
  · exact M.reg_range ⟨(le_of_not_ge h),hz.2⟩

lemma MatchedPair.arc_derivative (M : MatchedPair) {z : ℝ}
    (hz : z ∈ Icc M.axis.δ (endRadius M.sonic.e)) :
    HasDerivWithinAt M.arc (N (kap M.parameter) z (M.arc z)/D (sig M.parameter) z (M.arc z))
      (Icc M.axis.δ (endRadius M.sonic.e)) z := by
  apply ODEGlue.hasDerivWithinAt_join (f:=fun z u => N (kap M.parameter) z u/D (sig M.parameter) z u)
    (u:=M.middle) (v:=M.eul) (by linarith [M.axis.δ_lt])
    (endRadius_bounds M.sonic.e_pos M.sonic.e_lt).1.le
    (fun t ht => M.middle_derivative ht) (fun t ht => M.eul_derivative ht) _ z hz
  simp only [MatchedPair.middle,ODEGlue.join,show ¬(99/100:ℝ)≤9/10 by norm_num,ite_false,
    MatchedPair.reg,sub_self,MatchedPair.eul,coord_ninety_nine,M.sonic.v_start]

lemma MatchedPair.arc_range (M : MatchedPair) {z : ℝ}
    (hz : z ∈ Icc M.axis.δ (endRadius M.sonic.e)) : M.arc z ∈ Ioo (0:ℝ) 1 := by
  unfold MatchedPair.arc ODEGlue.join
  split_ifs with h
  · exact M.middle_range ⟨hz.1,h⟩
  · exact M.eul_range ⟨le_of_not_ge h,hz.2⟩

theorem MatchedPair.arc_smooth (M : MatchedPair) :
    ContDiffOn ℝ ∞ M.arc (Icc M.axis.δ (endRadius M.sonic.e)) :=
  ODEGlue.smooth_arc (f:=fun z u => N (kap M.parameter) z u/D (sig M.parameter) z u)
    (normalized_field_smooth M.parameter M.axis.δ_pos
    (endRadius_bounds M.sonic.e_pos M.sonic.e_lt).2.le)
    (fun _ hz => M.arc_derivative hz) (fun _ hz => M.arc_range hz)

end SepticProfile.SonicShooting

end
end

end OAI
