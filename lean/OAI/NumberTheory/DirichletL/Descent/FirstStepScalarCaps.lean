import OAI.NumberTheory.DirichletL.Descent.FirstDyadicRadius

namespace OAI

noncomputable section

namespace SevenEighths.InverseMoment

 theorem first_step_scalar_caps (Z A M r ell V delta aa bb rr t j eta tau window b:ℝ)
    (hZ:1<Z)(hA:0≤A)(hM:0≤M)(hMcap:M≤A)(hr: -1≤r)(hrcap:r≤A)
    (hell:0≤ell)(hellcap:ell≤A)(hV:0≤V)(hVcap:V≤A)
    (hd:0≤delta)(hdcap:delta≤A)(haa:0≤aa)(haacap:aa≤A)
    (hbb:0≤bb)(hbbcap:bb≤A)(hrr:0≤rr)(_hrrcap:rr≤A)
    (ht:0≤t)(_htcap:t≤A)(hj:0≤j)(hjcap:j≤A)
    (heta:0≤eta)(heta1:eta≤1)(htau:0≤tau)(htau1:tau≤1)
    (hwindow:Real.exp window≤Z^eta)(hb:b≤Z^eta):
    let X:=Z^(r-aa-bb-t);
    let Y:=Z^(firstPhysicalHeight M r ell V delta bb j+12*eta+tau);
    X*Real.exp window≤Z^(A+1) ∧ Y≤Z^(16*A+20) ∧ Y⁻¹≤Z^(4*A+2) ∧
    b*X≤Z^(16*A+20) ∧ delta+eta+2*(A+1)+tau+(4*A+2)≤16*A+20 ∧
    firstKappa M r ell V delta aa bb rr+(9/2:ℝ)*eta≤16*A+20 ∧
    (∀e:ℝ,e≤A→Z^(e+eta)≤Z^(16*A+20)):=by
  intro X Y
  have hz:0<Z:=zero_lt_one.trans hZ
  have hX:X≤Z^A:=Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have hX0:0≤X:=Real.rpow_nonneg hz.le _
  have hxy:X*Real.exp window≤Z^(A+1):=by
    calc
      _≤Z^A*Z^eta:=mul_le_mul hX hwindow (Real.exp_pos _).le (Real.rpow_nonneg hz.le _)
      _=Z^(A+eta):=(Real.rpow_add hz A eta).symm
      _≤Z^(A+1):=Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  refine ⟨hxy,?_,?_,?_,by linarith,?_,?_⟩
  · apply Real.rpow_le_rpow_of_exponent_le hZ.le
    unfold firstPhysicalHeight
    linarith
  · rw [show Y⁻¹=Z^(-(firstPhysicalHeight M r ell V delta bb j+12*eta+tau)) by
      dsimp [Y];rw [Real.rpow_neg hz.le]]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    unfold firstPhysicalHeight
    linarith
  · calc
      b*X≤Z^eta*Z^A:=mul_le_mul hb hX hX0 (Real.rpow_nonneg hz.le _)
      _=Z^(eta+A):=(Real.rpow_add hz eta A).symm
      _≤Z^(16*A+20):=Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  · unfold firstKappa
    linarith
  · intro e he
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    linarith

theorem first_step_scalar_losses (A r ell aa bb rr t eta pi em ed:ℝ)
    (hA:0≤A)(hr:r≤A)(hell:ell≤A)(haa:0≤aa)(_hbb:0≤bb)(hbbA:bb≤A)
    (hrr:rr≤A)(_ht:0≤t)(htA:t≤A)(_heta:0≤eta)(heta1:eta≤1)
    (he:0≤em)(hd:0≤ed)(hpi:0≤pi)(hetaPi:6*eta≤pi)
    (hem:em*(20*A+30)≤pi/4)(hed:ed*(20*A+30)≤pi/4):
    em*(ell+rr/2+t+(16*A+20)+11*eta/2)≤pi ∧
    em*(r-aa-bb-t)+7*eta/2+ed*(3*ell+bb+t+5*eta)+
      2*em*(2*ell+bb+t+4*eta)≤pi+eta/2:=by
  have hm:=mul_le_mul_of_nonneg_left (show ell+rr/2+t+(16*A+20)+11*eta/2≤20*A+30 by linarith) he
  have h1:=mul_le_mul_of_nonneg_left (show r-aa-bb-t+2*(2*ell+bb+t+4*eta)≤20*A+30 by linarith) he
  have h2:=mul_le_mul_of_nonneg_left (show 3*ell+bb+t+5*eta≤20*A+30 by linarith) hd
  constructor <;> nlinarith

end SevenEighths.InverseMoment

end

end OAI
