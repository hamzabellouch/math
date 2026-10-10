import OAI.NumberTheory.DirichletL.Descent.ActualDepthBudget
import OAI.NumberTheory.DirichletL.Descent.FirstTwoPassLowerRank

namespace OAI

noncomputable section

namespace SevenEighths.InverseMoment

def firstPassEpsilon (F eta:ℝ):ℝ:=eta/(10*F+32)
def sourceMassEpsilon (F eta:ℝ):ℝ:=2*eta/(20*(3*F+16)+30)

theorem actual_step_parameters (F eta r ell epsChild:ℝ)
    (hF:0≤F)(heta:0<eta)(heta1:eta≤1)(hr:r≤F)(hell:ell≤F)(heps:0≤epsChild):
    0<firstPassEpsilon F eta ∧ 0<sourceMassEpsilon F eta ∧
    6*eta≤8*eta ∧
    sourceMassEpsilon F eta*(20*(3*F+16)+30)≤(8*eta)/4 ∧
    48*eta+eta+8*eta+epsChild+eta≤epsChild+58*eta ∧
    3*eta+firstPassEpsilon F eta*(5*ell+2*r+7*eta)≤epsChild+60*eta ∧
    (epsChild+58*eta)+(2*F+15*eta+eta)*firstPassEpsilon F eta+firstPassEpsilon F eta≤epsChild+60*eta :=by
  have hd:0<10*F+32:=by positivity
  have hm:0<20*(3*F+16)+30:=by positivity
  have he:0<firstPassEpsilon F eta:=div_pos heta hd
  have heq:firstPassEpsilon F eta*(10*F+32)=eta:=by unfold firstPassEpsilon;field_simp
  have heq':sourceMassEpsilon F eta*(20*(3*F+16)+30)=2*eta:=by unfold sourceMassEpsilon;field_simp
  refine ⟨he,div_pos (by positivity) hm,by linarith,by linarith,by ring_nf;linarith,?_,?_⟩
  · have hcap:5*ell+2*r+7*eta≤10*F+32:=by linarith
    have hh:=mul_le_mul_of_nonneg_left hcap he.le
    nlinarith
  · have hcap:2*F+15*eta+eta+1≤10*F+32:=by linarith
    have hh:=mul_le_mul_of_nonneg_left hcap he.le
    nlinarith

theorem actual_long_rank_slack (cutoff eta ell V:ℝ)(hd:0<cutoff)(_he:0≤eta)
    (hsmall:eta≤cutoff/32)(hprogress:cutoff-eta≤ell+V):
    0<cutoff/2 ∧ cutoff/2≤ell+V ∧ eta≤(cutoff/2)/16 ∧ 17*eta≤cutoff :=by
  constructor
  · positivity
  constructor
  · linarith
  constructor <;> linarith

theorem actual_recursion_parameters (Mcap Fcap c eps:ℝ)(_hM:0≤Mcap)(_hF:0≤Fcap)(hc:0<c)(heps:0<eps):
    ∃cutoff eta:ℝ,0<cutoff ∧ 0<eta ∧ eta≤1 ∧ eta≤cutoff/32 ∧
      cutoff≤(c/2)/200 ∧ eta≤(c/2)/100000 ∧
      let depth:=actualDepth Mcap (cutoff/2);
      (depth:ℝ)*7*eta≤c/2 ∧ (depth:ℝ)*15*eta≤1 ∧
      (depth:ℝ)*100*eta≤eps/4 :=by
  let cutoff:=c/1000
  have hd:0<cutoff:=by dsimp[cutoff];positivity
  let depth:=actualDepth Mcap (cutoff/2)
  let D:ℝ:=(depth:ℝ)+1
  have hD:0<D:=by dsimp[D];positivity
  let eta:=min 1 (min (cutoff/32) (min (c/200000) (min (c/(28*D)) (min (1/(30*D)) (eps/(800*D))))))
  have he:0<eta:=by dsimp[eta];positivity
  have he1:eta≤1:=min_le_left _ _
  have he2:eta≤cutoff/32:=(min_le_right _ _).trans (min_le_left _ _)
  have he3:eta≤c/200000:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have he4:eta≤c/(28*D):=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have he5:eta≤1/(30*D):=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have he6:eta≤eps/(800*D):=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  refine ⟨cutoff,eta,hd,he,he1,he2,by dsimp[cutoff];linarith,by linarith,?_⟩
  have h4:eta*(28*D)≤c:=(le_div_iff₀ (by positivity)).mp he4
  have h5:eta*(30*D)≤1:=(le_div_iff₀ (by positivity)).mp he5
  have h6:eta*(800*D)≤eps:=(le_div_iff₀ (by positivity)).mp he6
  have hn:(depth:ℝ)*eta≤D*eta:=mul_le_mul_of_nonneg_right (by dsimp[D];linarith) he.le
  change (depth:ℝ)*7*eta≤c/2 ∧ (depth:ℝ)*15*eta≤1 ∧ (depth:ℝ)*100*eta≤eps/4
  constructor <;> first | nlinarith | constructor <;> nlinarith

end SevenEighths.InverseMoment

end

end OAI
