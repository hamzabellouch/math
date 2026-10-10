import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedUnitInflation

namespace OAI

/-! The finite ramified factor at every signed omega-unit. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaEisensteinWeight_signed_unit (e : Eisensteinˣ) (r j : ℕ)
    (he : (e:Eisenstein)=omegaE^r ∨ (e:Eisenstein)=-(omegaE^r)) (a : Eisenstein) :
    cubicThetaEisensteinWeight ((e:Eisenstein)*lambdaE^j) a=
      cubicThetaEisensteinWeight (lambdaE^j) a*(cubicSymbol a omegaE)^r := by
  rw [cubicThetaEisensteinWeight_unit_lambda,cubicThetaEisensteinWeight_lambda_pow]
  by_cases ha : primary a
  · rw [ite_eq_left ha,ite_eq_left ha]
    rcases he with he | he
    · rw [he,cubicSymbol_pow_upper ha]
      ring
    · rw [he,cubicSymbol_neg ha,cubicSymbol_pow_upper ha]
      ring
  · rw [ite_eq_right ha,ite_eq_right ha,zero_mul]

theorem cubicThetaUnitRamifiedBase_value (e : Eisensteinˣ) (r j : ℕ)
    (he : (e:Eisenstein)=omegaE^r ∨ (e:Eisenstein)=-(omegaE^r)) (h : Eisenstein) :
    cubicThetaUnitRamifiedBase e j h=
      cubicThetaRamifiedUnitNineGauss j r (-(((e⁻¹:Eisensteinˣ):Eisenstein))*h) := by
  let d : Eisenstein := 3*(e:Eisenstein)*lambdaE^2
  have hd : d= -9*(e:Eisenstein) := by dsimp only [d]; rw [lambdaE_sq]; ring
  have hd0 : d≠0 := mul_ne_zero (mul_ne_zero (by norm_num) e.ne_zero)
    (pow_ne_zero _ lambdaE_prime.ne_zero)
  have hmod : modulus d=modulus (9:Eisenstein) := by
    apply le_antisymm
    · apply Ideal.span_singleton_le_span_singleton.mpr
      exact ⟨-(e:Eisenstein),by rw [hd]; ring⟩
    · apply Ideal.span_singleton_le_span_singleton.mpr
      refine ⟨-((e⁻¹:Eisensteinˣ):Eisenstein),?_⟩
      rw [hd]
      calc
        (9:Eisenstein) = 9*((e:Eisenstein)*((e⁻¹:Eisensteinˣ):Eisenstein)) := by
          rw [e.mul_inv,mul_one]
        _ = (-9*(e:Eisenstein))*(-((e⁻¹:Eisensteinˣ):Eisenstein)) := by ring
  let E : Residues d ≃+* Residues (9:Eisenstein) := Ideal.quotEquivOfEq hmod
  have hr (x : Residues d) : Ideal.Quotient.mk (modulus (9:Eisenstein))
      (residueRepresentative d x)=E x := by
    rw [← Ideal.quotEquivOfEq_mk hmod,residueRepresentative_spec]
  have hw (x : Residues d) :
      cubicThetaEisensteinWeight ((e:Eisenstein)*lambdaE^j) (residueRepresentative d x)=
      cubicThetaEisensteinWeight (lambdaE^j) (residueRepresentative 9 (E x))*
        (cubicSymbol (residueRepresentative 9 (E x)) omegaE)^r := by
    have h9 : (9:Eisenstein) ∣ residueRepresentative d x-residueRepresentative 9 (E x) := by
      apply Ideal.mem_span_singleton.mp
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_sub]
      exact sub_eq_zero.mpr ((hr x).trans (residueRepresentative_spec 9 (E x)).symm)
    rw [cubicThetaEisensteinWeight_unit_lambda_congr e j h9,
      cubicThetaEisensteinWeight_signed_unit e r j he]
  have ht (a : Eisenstein) :
      residueFourierChar d hd0 (Ideal.Quotient.mk (modulus d) (h*a))=
      residueFourierChar 9 (by norm_num)
        (Ideal.Quotient.mk (modulus 9) ((-(((e⁻¹:Eisensteinˣ):Eisenstein))*h)*a)) := by
    rw [residueFourierChar_mk,residueFourierChar_mk]
    congr 2
    unfold tracePair
    congr 2
    have hc : (d:ℂ)= -9*((e:Eisenstein):ℂ) := by
      calc
        (d:ℂ)=((-9*(e:Eisenstein):Eisenstein):ℂ) := congrArg (fun z : Eisenstein => (z:ℂ)) hd
        _ = _ := rfl
    have hi : (((e⁻¹:Eisensteinˣ):Eisenstein):ℂ)=(((e:Eisenstein):ℂ))⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      have hx := congrArg (fun z : Eisenstein => (z:ℂ)) e.inv_mul
      simpa only [Subalgebra.coe_mul,Subalgebra.coe_one] using hx
    have hne : ((e:Eisenstein):ℂ)≠0 := fun hzero => e.ne_zero (Subtype.ext hzero)
    rw [hc]
    push_cast
    rw [hi]
    change (h:ℂ)*(a:ℂ)*(1/(-9*((e:Eisenstein):ℂ)*traceLambda))=
      (-(((e:Eisenstein):ℂ)⁻¹)*(h:ℂ)*(a:ℂ))*(1/(9*traceLambda))
    field_simp [hne,traceLambda_ne_zero]
  have hp (x : Residues d) :
      residueFourierChar d hd0 (Ideal.Quotient.mk (modulus d) h*x)=
      residueFourierChar 9 (by norm_num)
        (Ideal.Quotient.mk (modulus 9) (-(((e⁻¹:Eisensteinˣ):Eisenstein))*h)*E x) := by
    calc
      _ = residueFourierChar d hd0 (Ideal.Quotient.mk (modulus d) (h*residueRepresentative d x)) := by
        congr 1
        rw [map_mul,residueRepresentative_spec]
      _ = _ := by rw [ht,map_mul,hr]
  unfold cubicThetaUnitRamifiedBase cubicThetaRamifiedUnitNineGauss
  change (∑' x : Residues d, cubicThetaEisensteinWeight ((e:Eisenstein)*lambdaE^j)
    (residueRepresentative d x)*residueFourierChar d hd0
      (Ideal.Quotient.mk (modulus d) h*x))=_
  rw [← E.toEquiv.tsum_eq]
  apply tsum_congr
  intro x
  rw [hw,hp]
  rfl

end CubicFirstMoment

end

end OAI
