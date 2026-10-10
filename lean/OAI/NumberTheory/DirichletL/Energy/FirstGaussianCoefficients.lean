import OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedFourCoefficients
import OAI.NumberTheory.DirichletL.Moments.SecondSourceSeededPowerDescent

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyFirstGaussianCoefficients
open HeckeFamily CenteredMomentFiniteProfileExceptional
open CenteredMomentSecondChildPowerBudget CenteredMomentSecondSourceSeededPowerDescent
open CenteredMomentSecondSourcePowerDescent CenteredMomentSecondWindowBudget
open CenteredMomentFirstAmplifiedFourCoefficients CenteredMomentSourceInputTailUniform
local notation "O"=>HeckeFamily.O

def fixedFactors (Cm Ce Cd Ct Z epsilon delta theta B cost Ebase t loFloor seed:ℝ)
    (J:ℕ)(Sf:Finset (ℕ×ℕ))(W:𝓢(ℝ,ℂ)):Fin 4→ℝ:=
  ![Cm*Z^(2*delta+epsilon)*cost*Ebase*heightEnvelope t^(J+J)*profileMoment J*profileMoment J,
    Ce*Z^(2*epsilon+2*delta+2*(5*B+1)*theta)*loFloor^(-2/3:ℝ),
    Cd*‖EisensteinSchwartzPoisson.paperRadialFourier W 0‖,
    Ct*Sf.sup (schwartzSeminormFamily ℝ ℝ ℂ) W/seed]

lemma coefficients_mul {a b:ℝ}(N:ℕ)(upper b1 b2 A:ℝ)(Sp:Finset (ℕ×ℕ))
    (p:Profiles a b)(J:ℕ)(Q:Ideal O)(K t epsilon seed:ℝ)(f g:Fin 4→ℝ):
    ∀j,CenteredMomentSecondChildPowerBudget.coefficients N upper b1 b2 A Sp p J Q K t epsilon seed (fun j=>f j*g j) j=
      CenteredMomentSecondChildPowerBudget.coefficients N upper b1 b2 A Sp p J Q K t epsilon seed f j*g j:=by
  intro j
  fin_cases j <;> simp [CenteredMomentSecondChildPowerBudget.coefficients] <;> ring

lemma coefficients_mono {a b:ℝ}(N:ℕ)(upper b1 b2 A:ℝ)(Sp:Finset (ℕ×ℕ))
    (p:Profiles a b)(J:ℕ)(Q:Ideal O)(K t epsilon seed:ℝ)(f g:Fin 4→ℝ)
    (hu:0≤upper)(hb1:0≤b1)(hb2:0≤b2)(hK:0≤K)(hseed:0≤seed)
    (hfg:∀j,f j≤g j):
    ∀j,CenteredMomentSecondChildPowerBudget.coefficients N upper b1 b2 A Sp p J Q K t epsilon seed f j≤
      CenteredMomentSecondChildPowerBudget.coefficients N upper b1 b2 A Sp p J Q K t epsilon seed g j:=by
  have h0:=hfg 0
  have h1:=hfg 1
  have h2:=hfg 2
  have h3:=hfg 3
  intro j
  fin_cases j <;> simp only [CenteredMomentSecondChildPowerBudget.coefficients, Fin.isValue, Matrix.cons_val,  Fin.reduceFinMk]
  · gcongr
  · have he:0≤CenteredMomentFirstChildProfileControl.exceptionalConstant N upper J Q K:=by
      unfold CenteredMomentFirstChildProfileControl.exceptionalConstant
      positivity
    gcongr
  · gcongr
  · gcongr

theorem seeded_factors_main (Cm Ce Cd Ct Z epsilon delta theta B saving radius t q cost Ebase
    ell deficit paid r loProduct wlo loFloor seed:ℝ)(J:ℕ)
    (Sf:Finset (ℕ×ℕ))(W:𝓢(ℝ,ℂ))
    (_hCm:0≤Cm)(hCe:0≤Ce)(hZ:0<Z)(hE:0≤Ebase)(hradius:0≤radius)
    (hlo:0<loFloor)(hloProduct:loFloor≤loProduct*wlo*wlo):
    let E:=Ebase*Z^(ell+deficit/6+paid);
    ∀j,seededFactors Cm Ce Cd Ct Z epsilon delta theta B saving radius t (cost*q)
        E E r loProduct wlo seed J J Sf W j≤
      fixedFactors Cm Ce Cd Ct Z epsilon delta theta B cost Ebase t loFloor seed J Sf W j*
        mainPowers q Z radius ell deficit paid saving r j:=by
  dsimp only
  have hEp:0≤Ebase*Z^(ell+deficit/6+paid):=mul_nonneg hE (Real.rpow_nonneg hZ.le _)
  have hsqrt:Real.sqrt ((Ebase*Z^(ell+deficit/6+paid))*(Ebase*Z^(ell+deficit/6+paid)))=
      Ebase*Z^(ell+deficit/6+paid):=by rw [←pow_two,Real.sqrt_sq hEp]
  have hneg:(loProduct*wlo*wlo)^(-2/3:ℝ)≤loFloor^(-2/3:ℝ):=
    Real.rpow_le_rpow_of_nonpos hlo hloProduct (by norm_num)
  intro j
  fin_cases j
  · simp only [seededFactors,physicalFactors,fixedFactors,mainPowers,Fin.isValue,Matrix.cons_val,Fin.reduceFinMk,hsqrt]
    exact le_of_eq (by ring)
  · simp only [seededFactors,physicalFactors,fixedFactors,mainPowers,Fin.isValue,Matrix.cons_val,Fin.reduceFinMk]
    rw [Real.rpow_sub hZ]
    have hbase:0≤Ce*Z^(2*epsilon+2*delta+2*(5*B+1)*theta)/Z^(2*max r 0/3)*radius^(5/6:ℝ):=by positivity
    have hh:=mul_le_mul_of_nonneg_left hneg hbase
    have hpow:Z^(-2*max r 0/3)=(Z^(2*max r 0/3))⁻¹:=by
      rw [show -2*max r 0/3=-(2*max r 0/3) by ring,Real.rpow_neg hZ.le]
    convert hh using 1 <;> (try rw [hpow]) <;> ring
  · simp [seededFactors,physicalFactors,fixedFactors,mainPowers,mul_comm,mul_left_comm,mul_assoc]
  · simp only [seededFactors,physicalFactors,fixedFactors,mainPowers,Fin.isValue,Matrix.cons_val,Fin.reduceFinMk]
    exact le_of_eq (by ring)

lemma fixedFactors_nonneg (Cm Ce Cd Ct Z epsilon delta theta B cost Ebase t loFloor seed:ℝ)
    (J:ℕ)(Sf:Finset (ℕ×ℕ))(W:𝓢(ℝ,ℂ))
    (hCm:0≤Cm)(hCe:0≤Ce)(hCd:0≤Cd)(hCt:0≤Ct)(hZ:0≤Z)
    (hcost:0≤cost)(hE:0≤Ebase)(hlo:0≤loFloor)(hseed:0≤seed):
    ∀j,0≤fixedFactors Cm Ce Cd Ct Z epsilon delta theta B cost Ebase t loFloor seed J Sf W j:=by
  have hh:0≤heightEnvelope t:=(heightEnvelope_pos t).le
  have hp:=profileMoment_nonneg J
  have hc:0≤Sf.sup (schwartzSeminormFamily ℝ ℝ ℂ) W:=apply_nonneg _ _
  intro j
  fin_cases j <;> simp only [fixedFactors,Matrix.cons_val,Fin.reduceFinMk] <;> positivity

theorem main_coefficients {a b:ℝ}(N:ℕ)(upper b1 b2 A:ℝ)(Sp:Finset (ℕ×ℕ))
    (p:Profiles a b)(Jprofile:ℕ)(Q:Ideal O)(Kfix:ℝ)
    (Cm Ce Cd Ct Z epsilon delta theta B saving radius t q cost Ebase
      ell deficit paid r loProduct wlo loFloor seed:ℝ)(J:ℕ)
    (Sf:Finset (ℕ×ℕ))(W:𝓢(ℝ,ℂ))
    (hu:0≤upper)(hb1:0≤b1)(hb2:0≤b2)(hK:0≤Kfix)(hseed:0≤seed)
    (hCm:0≤Cm)(hCe:0≤Ce)(hZ:0<Z)(hE:0≤Ebase)(hradius:0≤radius)
    (hlo:0<loFloor)(hloProduct:loFloor≤loProduct*wlo*wlo):
    let E:=Ebase*Z^(ell+deficit/6+paid);
    let H:=CenteredMomentSecondChildPowerBudget.coefficients N upper b1 b2 A Sp p Jprofile Q Kfix t epsilon seed
      (fixedFactors Cm Ce Cd Ct Z epsilon delta theta B cost Ebase t loFloor seed J Sf W);
    ∀j,CenteredMomentSecondChildPowerBudget.coefficients N upper b1 b2 A Sp p Jprofile Q Kfix t epsilon seed
      (seededFactors Cm Ce Cd Ct Z epsilon delta theta B saving radius t (cost*q)
        E E r loProduct wlo seed J J Sf W) j≤
      H j*mainPowers q Z radius ell deficit paid saving r j:=by
  dsimp only
  have hh:=coefficients_mono N upper b1 b2 A Sp p Jprofile Q Kfix t epsilon seed _ _
    hu hb1 hb2 hK hseed
    (seeded_factors_main Cm Ce Cd Ct Z epsilon delta theta B saving radius t q cost Ebase
      ell deficit paid r loProduct wlo loFloor seed J Sf W hCm hCe hZ hE hradius hlo hloProduct)
  intro j
  exact (hh j).trans_eq (coefficients_mul N upper b1 b2 A Sp p Jprofile Q Kfix t epsilon seed _ _ j)

theorem error_coefficients {a b:ℝ}(N:ℕ)(upper b1 b2 A:ℝ)(Sp:Finset (ℕ×ℕ))
    (profiles:Profiles a b)(Jprofile:ℕ)(Q:Ideal O)(Kfix:ℝ)(prime:O)(k:ℕ)
    (Cm Ce Cd Ct Z epsilon delta theta B saving radius t q cost Ebase
      deficit paid r loProduct wlo loFloor seed:ℝ)(J:ℕ)
    (Sf:Finset (ℕ×ℕ))(W:𝓢(ℝ,ℂ))
    (hu:0≤upper)(hb1:0≤b1)(hb2:0≤b2)(hK:0≤Kfix)(hseed:0≤seed)
    (hCm:0≤Cm)(hCe:0≤Ce)(hZ:0<Z)(hE:0≤Ebase)(hradius:0≤radius)
    (hlo:0<loFloor)(hloProduct:loFloor≤loProduct*wlo*wlo):
    let E:=Ebase*Z^(CenteredMomentFirstAmplificationChoice.errorRemoval prime Z k+deficit/6+paid);
    let H:=CenteredMomentSecondChildPowerBudget.coefficients N upper b1 b2 A Sp profiles Jprofile Q Kfix t epsilon seed
      (fixedFactors Cm Ce Cd Ct Z epsilon delta theta B cost Ebase t loFloor seed J Sf W);
    ∀j,CenteredMomentSecondChildPowerBudget.coefficients N upper b1 b2 A Sp profiles Jprofile Q Kfix t epsilon seed
      (seededFactors Cm Ce Cd Ct Z epsilon delta theta B saving radius t
        (cost*q*Z^(CenteredMomentFirstAmplificationChoice.errorMoving prime Z k))
        E E r loProduct wlo seed J J Sf W) j≤
      H j*errorPowers prime k q Z radius deficit paid saving r j:=by
  dsimp only
  have hh:=main_coefficients N upper b1 b2 A Sp profiles Jprofile Q Kfix
    Cm Ce Cd Ct Z epsilon delta theta B saving radius t
    (q*Z^(CenteredMomentFirstAmplificationChoice.errorMoving prime Z k)) cost Ebase
    (CenteredMomentFirstAmplificationChoice.errorRemoval prime Z k) deficit paid r
    loProduct wlo loFloor seed J Sf W hu hb1 hb2 hK hseed hCm hCe hZ hE hradius hlo hloProduct
  intro j
  have hid:mainPowers (q*Z^(CenteredMomentFirstAmplificationChoice.errorMoving prime Z k)) Z radius
      (CenteredMomentFirstAmplificationChoice.errorRemoval prime Z k) deficit paid saving r j=
      errorPowers prime k q Z radius deficit paid saving r j:=by
    fin_cases j <;> rfl
  have hhj:=hh j
  rw [hid] at hhj
  simpa only [mul_assoc] using hhj

end SevenEighths.CenteredMomentEnergyFirstGaussianCoefficients

end

end OAI
