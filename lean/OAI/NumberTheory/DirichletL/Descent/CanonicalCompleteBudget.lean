import OAI.NumberTheory.DirichletL.Descent.CanonicalLongCosts
import OAI.NumberTheory.DirichletL.Descent.RecursionParameters

namespace OAI

noncomputable section

namespace SevenEighths.InverseMoment

theorem actual_complete_step_cost (L eta epsChild:ℝ)(hL:0≤L)(heta:0<eta)
    (heta1:eta≤1)(heps:0≤epsChild):
    3*eta+firstPassEpsilon L eta*(2*L+7*eta)≤epsChild+60*eta ∧
    2*L*firstPassEpsilon L eta≤eta ∧
    (epsChild+60*eta)+2*L*firstPassEpsilon L eta+eta≤epsChild+62*eta := by
  have hd:0<10*L+32:=by positivity
  have hp:0<firstPassEpsilon L eta:=div_pos heta hd
  have he:firstPassEpsilon L eta*(10*L+32)=eta:=by unfold firstPassEpsilon;field_simp
  have hb:2*L+7*eta≤10*L+32:=by linarith
  have hc:=mul_le_mul_of_nonneg_left hb hp.le
  have hl:=mul_le_mul_of_nonneg_left (show 2*L≤10*L+32 by linarith) hp.le
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem actual_complete_height_merge (dshort dlong:ℕ)(Z F cstar loss Cs Cb A theta:ℝ)
    (hZ:1≤Z)(hcstar:0≤cstar)(hloss:0≤loss)(hCs:0≤Cs)(hCb:0≤Cb)(hA:0≤A):
    Cs*(1+‖theta‖)^dshort*Z^(F-cstar/256)+
      Cb*(1+A)*(1+‖theta‖)^dlong*Z^(F+loss)≤
    (Cs+Cb)*(1+A)*(1+‖theta‖)^(max dshort dlong)*Z^(F+loss) := by
  have hp:1≤1+‖theta‖:=by linarith [norm_nonneg theta]
  have hshort:(1+‖theta‖)^dshort≤(1+‖theta‖)^(max dshort dlong):=
    pow_le_pow_right₀ hp (le_max_left _ _)
  have hlong:(1+‖theta‖)^dlong≤(1+‖theta‖)^(max dshort dlong):=
    pow_le_pow_right₀ hp (le_max_right _ _)
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hs:Z^(F-cstar/256)≤Z^(F+loss):=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hs':Cs*(1+‖theta‖)^dshort*Z^(F-cstar/256)≤
      Cs*(1+A)*(1+‖theta‖)^(max dshort dlong)*Z^(F+loss):=by
    calc
      _≤Cs*(1+‖theta‖)^(max dshort dlong)*Z^(F+loss):=by gcongr
      _≤_:=by
        have hh:Cs≤Cs*(1+A):=by nlinarith
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh (by positivity)) (by positivity)
  have hl':Cb*(1+A)*(1+‖theta‖)^dlong*Z^(F+loss)≤
      Cb*(1+A)*(1+‖theta‖)^(max dshort dlong)*Z^(F+loss):=by gcongr
  have hh:=add_le_add hs' hl'
  convert hh using 1 ; ring

end SevenEighths.InverseMoment

end

end OAI
