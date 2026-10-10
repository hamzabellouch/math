import Mathlib

namespace OAI

section

noncomputable section
namespace WeakMTWTransport

lemma switch_numerical_errors {b r R D C H S eta:ℝ}
    (hb:0 < b) (hD:0 < D) (hr:0 ≤ r) (hC:0 ≤ C) (hH:0 ≤ H) (hS:0 ≤ S)
    (heta:eta ≤ 1/128) (hrb:r ≤ b/2048)
    (hR:b*(H+100) ≤ R) (hbD:b*(16*H+1000) ≤ D)
    (hquad:b*(C+1)*(S+1) ≤ D^2/1048576) :
    r ≤ b/4 ∧ b ≤ D/16 ∧
    b*H+2*r+6*D*(8*b/D)+(C*S)*(8*b/D)^2 ≤ R ∧
    4*eta*D+2*r+12*D*(8*b/D)+2*(C*S)*(8*b/D)^2+b ≤ D ∧
    2*(C*S)*(8*b/D) ≤ 2*D ∧
    2*(8*b/D)*S+2*b*H+2*r ≤ D/4 ∧
    r+(C+1)*(8*b/D)^2*S ≤ b/1024 := by
  have hDp:0 < D^2:=sq_pos_of_pos hD
  have hCS:0 ≤ (C+1)*S:=by positivity
  have hcore:b*((C+1)*S) ≤ D^2/1048576:=by nlinarith only [hquad,mul_nonneg hb.le (by linarith only [hC] : 0 ≤ C+1)]
  have hkin:b*S ≤ D^2/1048576:=by
    have hh:0 ≤ b*C*S:=by positivity
    nlinarith only [hcore,hh]
  have htem: (C+1)*(8*b/D)^2*S ≤ b/16384 := by
    have hh:=mul_le_mul_of_nonneg_right hcore (show 0 ≤ 64*b/D^2 by positivity)
    have he:(b*((C+1)*S))*(64*b/D^2)=(C+1)*(8*b/D)^2*S:=by ring
    have he':(D^2/1048576)*(64*b/D^2)=b/16384:=by field_simp; ring
    rwa [he,he'] at hh
  have htemC:(C*S)*(8*b/D)^2 ≤ b/16384:=by
    have hp:0 ≤ S*(8*b/D)^2:=by positivity
    nlinarith only [htem,hp]
  have hlinS:2*(8*b/D)*S ≤ D/65536:=by
    have hh:=mul_le_mul_of_nonneg_right hkin (show 0 ≤ 16/D by positivity)
    have he:(b*S)*(16/D)=2*(8*b/D)*S:=by ring
    have he':(D^2/1048576)*(16/D)=D/65536:=by field_simp; ring
    rwa [he,he'] at hh
  have hlinC:2*(C*S)*(8*b/D) ≤ D/65536:=by
    have hh:=mul_le_mul_of_nonneg_right hcore (show 0 ≤ 16/D by positivity)
    have he':(D^2/1048576)*(16/D)=D/65536:=by field_simp; ring
    rw [he'] at hh
    have hpos:0 ≤ 16*b*S/D:=by positivity
    calc
      2*(C*S)*(8*b/D) = b*((C+1)*S)*(16/D)-16*b*S/D := by ring
      _ ≤ D/65536 := by linarith only [hh,hpos]
  have he6:6*D*(8*b/D)=48*b:=by field_simp; ring
  have he12:12*D*(8*b/D)=96*b:=by field_simp; ring
  have heEta:=mul_le_mul_of_nonneg_right heta hD.le
  have hbH:0 ≤ b*H:=mul_nonneg hb.le hH
  refine ⟨by linarith only [hrb,hr],by nlinarith only [hbD,hbH,hb],?_,?_,?_,?_,?_⟩
  · rw [he6]
    nlinarith only [hR,hrb,htemC,hb]
  · rw [he12]
    nlinarith only [heEta,hrb,htemC,hbD,hbH,hb]
  · linarith only [hlinC,hD]
  · nlinarith only [hlinS,hbD,hrb,hb,hD]
  · linarith only [hrb,htem,hb]

end WeakMTWTransport

end
end

end OAI
