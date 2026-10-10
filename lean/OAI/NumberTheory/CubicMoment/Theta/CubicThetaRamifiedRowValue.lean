import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedUnitGauss

namespace OAI

/-! The computed modulus-nine sum in the normalization of the actual
Eisenstein rows. The sign comes from lambda squared being minus three. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cubicThetaRamifiedBaseRow_one (j : ℕ) (h : Eisenstein) :
    cubicThetaRamifiedBaseRow 1 one_ne_zero j h=cubicThetaRamifiedNineGauss j (-h) := by
  let d : Eisenstein := 3*lambdaE^2*1
  have hd : d=(-9:Eisenstein) := by dsimp only [d]; rw [lambdaE_sq]; ring
  have hd0 : d≠0 := by rw [hd]; norm_num
  have hmod : modulus d=modulus (9:Eisenstein) := by
    rw [hd]
    exact Ideal.span_singleton_neg (x:=(9:Eisenstein))
  let e : Residues d ≃+* Residues (9:Eisenstein) := Ideal.quotEquivOfEq hmod
  have hr (x : Residues d) : Ideal.Quotient.mk (modulus (9:Eisenstein))
      (residueRepresentative d x)=e x := by
    rw [← Ideal.quotEquivOfEq_mk hmod,residueRepresentative_spec]
  have hw (x : Residues d) :
      cubicThetaEisensteinWeight (lambdaE^j) (residueRepresentative d x)=
      cubicThetaEisensteinWeight (lambdaE^j) (residueRepresentative 9 (e x)) := by
    have he : (9:Eisenstein) ∣ residueRepresentative d x-residueRepresentative 9 (e x) := by
      apply Ideal.mem_span_singleton.mp
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_sub]
      exact sub_eq_zero.mpr ((hr x).trans (residueRepresentative_spec 9 (e x)).symm)
    have he' : (9:Eisenstein)*1 ∣ residueRepresentative d x-residueRepresentative 9 (e x) := by
      simpa only [mul_one] using he
    simpa only [mul_one] using cubicThetaEisensteinWeight_ramified_congr primary_one j he' 
  have ht (a : Eisenstein) :
      residueFourierChar d hd0 (Ideal.Quotient.mk (modulus d) (h*a))=
      residueFourierChar 9 (by norm_num) (Ideal.Quotient.mk (modulus 9) ((-h)*a)) := by
    rw [residueFourierChar_mk,residueFourierChar_mk]
    congr 2
    unfold tracePair
    congr 2
    have hc : (d:ℂ)=(-9:ℂ) := by
      calc
        (d:ℂ)=((-9:Eisenstein):ℂ) := congrArg (fun z : Eisenstein => (z:ℂ)) hd
        _ = (-9:ℂ) := rfl
    rw [hc]
    push_cast
    change (h:ℂ)*(a:ℂ)*(1/((-9)*traceLambda))=
      (-(h:ℂ)*(a:ℂ))*(1/(9*traceLambda))
    field_simp [traceLambda_ne_zero]
  have hp (x : Residues d) :
      residueFourierChar d hd0 (Ideal.Quotient.mk (modulus d) h*x)=
      residueFourierChar 9 (by norm_num) (Ideal.Quotient.mk (modulus 9) (-h)*e x) := by
    calc
      _ = residueFourierChar d hd0
          (Ideal.Quotient.mk (modulus d) (h*residueRepresentative d x)) := by
        congr 1
        rw [map_mul,residueRepresentative_spec]
      _ = residueFourierChar 9 (by norm_num)
          (Ideal.Quotient.mk (modulus 9) ((-h)*residueRepresentative d x)) := ht _
      _ = _ := by rw [map_mul,hr]
  unfold cubicThetaRamifiedBaseRow cubicThetaRamifiedNineGauss
  change (∑' x : Residues d, cubicThetaEisensteinWeight (lambdaE^j*1)
    (residueRepresentative d x)*residueFourierChar d hd0
      (Ideal.Quotient.mk (modulus d) h*x))=_
  rw [← e.toEquiv.tsum_eq]
  apply tsum_congr
  intro x
  rw [mul_one,hw,hp]
  rfl

theorem cubicThetaEisensteinGaussCoefficient_ramified_value (n : ℕ) (h : Eisenstein) :
    cubicThetaEisensteinGaussCoefficient (lambdaE^(n+2)) (lambdaE^n*h)=
      (norm (lambdaE^n):ℂ)*
        (if (3:Eisenstein) ∣ -h+2*(((n+2)%3:ℕ):Eisenstein) then
          9*residueFourierChar 9 (by norm_num) (Ideal.Quotient.mk (modulus 9) (-h))
        else 0) := by
  have he := cubicThetaEisensteinGaussCoefficient_ramified_inflation primary_one n h
  simpa only [mul_one,cubicThetaRamifiedBaseRow_one,cubicThetaRamifiedNineGauss_eq] using he

end CubicFirstMoment

end

end OAI
