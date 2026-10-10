import OAI.NumberTheory.DirichletL.Descent.CanonicalCompleteState
import OAI.NumberTheory.DirichletL.Descent.CanonicalLongGeometry

namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.InverseMoment

theorem actual_long_coefficient_cost (Z ell L epsilon Ccoef:ℝ)
    (hZ:1≤Z)(hell:ell≤L)(heps:0≤epsilon):
    (Ccoef*(Real.exp 1*Z^ell)^epsilon)^2≤
      Ccoef^2*Real.exp (2*epsilon)*Z^(2*L*epsilon) := by
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hex:(Real.exp 1)^epsilon=Real.exp epsilon:=by rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp,one_mul]
  have hex2:(Real.exp epsilon)^2=Real.exp (2*epsilon):=by rw [←Real.exp_nat_mul];norm_num
  have hid:(Ccoef*(Real.exp 1*Z^ell)^epsilon)^2=
      Ccoef^2*Real.exp (2*epsilon)*Z^(2*ell*epsilon) := by
    rw [Real.mul_rpow (Real.exp_pos _).le (Real.rpow_nonneg hz.le _),hex,
      ←Real.rpow_mul hz.le,mul_pow,mul_pow,hex2,
      ←Real.rpow_mul_natCast hz.le]
    ring_nf
  rw [hid]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le hZ
  nlinarith

theorem actual_long_uniform_parent_cost (Z ell N V L epsilon Ccoef C A loss:ℝ)
    (hZ:1≤Z)(hell:ell≤L)(heps:0≤epsilon)(hC:0≤C)(hA:0≤A):
    C*(Ccoef*(Real.exp 1*Z^ell)^epsilon)^2*(1+A)*Z^((N-3*ell)+3*ell+V+loss)≤
      (C*Ccoef^2*Real.exp (2*epsilon))*(1+A)*Z^(N+V+loss+2*L*epsilon) := by
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have h:=actual_long_coefficient_cost Z ell L epsilon Ccoef hZ hell heps
  have hh:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left h hC) (by linarith:0≤1+A))
    (Real.rpow_nonneg hz.le ((N-3*ell)+3*ell+V+loss))
  apply hh.trans_eq
  have hpow:Z^(2*L*epsilon)*Z^((N-3*ell)+3*ell+V+loss)=Z^(N+V+loss+2*L*epsilon):=by
    rw [←Real.rpow_add hz];congr 1;ring
  calc
    _=(C*Ccoef^2*Real.exp (2*epsilon))*(1+A)*
        (Z^(2*L*epsilon)*Z^((N-3*ell)+3*ell+V+loss)):=by ring
    _=_:=by rw [hpow]

theorem complete_state_power_absorption (Z F cstar eps loss C A height E:ℝ)
    (hZ:1≤Z)(hc:0≤cstar)(heps:0≤eps)(hloss:0≤loss)
    (hC:0≤C)(_hA:0≤A)(hheight:0≤height)
    (hE:E≤A*height*Z^(F+loss)):
    C*(height*Z^(F-cstar/256)+Z^eps*E)≤
      C*(1+A)*height*Z^(F+loss+eps) := by
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hs:height*Z^(F-cstar/256)≤height*Z^(F+loss+eps):=by
    apply mul_le_mul_of_nonneg_left _ hheight
    exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have ht:Z^eps*E≤A*height*Z^(F+loss+eps):=by
    have hh:=mul_le_mul_of_nonneg_left hE (Real.rpow_nonneg hz.le eps)
    apply hh.trans_eq
    rw [Real.rpow_add hz (F+loss) eps]
    ring
  have hh:=mul_le_mul_of_nonneg_left (add_le_add hs ht) hC
  convert hh using 1 ; ring

end SevenEighths.InverseMoment

end

end OAI
