import OAI.NumberTheory.DirichletL.PrimeRows.RestoreCorrection
import OAI.NumberTheory.DirichletL.PrimeRows.CentralNormalized
import OAI.NumberTheory.DirichletL.PrimeRows.CentralRamified

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss

def centralNormalizedSlot (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) : ℂ :=
  continuedCompensatedLocal η u P hs x w z
    (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w)) /
    supportedCorrection η u P x w z

def repeatedRowPrime (u : FreeRow) (P : PrimeIdeal) : Prop :=
  P.val∣Ideal.span {u.val} ∧ 2≤multiplicity (primaryGenerator P.val) u.val

def centralRegularError (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) : ℂ :=
  if repeatedRowPrime u P then 0 else
    centralNormalizedSlot η u P hs x w z+star (idealRowHom u.val P.val)

def centralRepeatedTerm (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) : ℂ :=
  if repeatedRowPrime u P then centralNormalizedSlot η u P hs x w z else 0

theorem centralNormalizedSlot_split (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) :
    centralNormalizedSlot η u P hs x w z=
      -star (idealRowHom u.val P.val)+centralRegularError η u P hs x w z+
        centralRepeatedTerm η u P hs x w z := by
  by_cases hp : repeatedRowPrime u P
  · simp only [centralRegularError,centralRepeatedTerm,ite_eq_left hp,row_phase_ramified u P hp.1,
      star_zero,neg_zero,zero_add]
  · simp only [centralRegularError,centralRepeatedTerm,ite_eq_right hp]
    ring

theorem central_actual_local_bounds (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hη : IsCoprime P.val η.modulus)
    (a e : ℝ) (x w z : ℂ) (hQ : (480:ℝ)≤P.val.absNorm)
    (hsmall : 198*(P.val.absNorm:ℝ)^(-10*e)≤1/2)
    (ha : (51/100:ℝ)≤a) (ha1 : a≤1) (he : 0<e) (he1 : e≤1/1000)
    (hx : x.re=a+16*e) (hw : w.re=1-a-6*e) (hz : z.re=17/50) :
    1/2≤‖supportedCorrection η u P x w z‖ ∧
    ‖centralRegularError η u P hs x w z‖≤
      1440*(if P.val∣Ideal.span {u.val} then (P.val.absNorm:ℝ)^(1/2:ℝ)
        else (P.val.absNorm:ℝ)^(-(51/100:ℝ))) ∧
    ‖centralRepeatedTerm η u P hs x w z‖≤
      if repeatedRowPrime u P then 812*(P.val.absNorm:ℝ)^(1-w.re) else 0 := by
  have hQ0 : (0:ℝ)<P.val.absNorm := by linarith
  have hQ1 : (1:ℝ)≤P.val.absNorm := by linarith
  by_cases hd : P.val∣Ideal.span {u.val}
  · have hb := actual_central_ramified_normalized η u P hs hd (by linarith)
      a e x w z hsmall ha ha1 he he1 hx hw hz
    have hcorr : supportedCorrection η u P x w z=ramifiedCorrection η u P hs x w z := by
      simp [supportedCorrection,hs,hd]
    refine ⟨hcorr.symm ▸ hb.1,?_,?_⟩
    · by_cases hj : 2≤multiplicity (primaryGenerator P.val) u.val
      · simp [centralRegularError,repeatedRowPrime,hd,hj]
        positivity
      · have hp : ¬repeatedRowPrime u P := fun h=>hj h.2
        rw [centralRegularError,ite_eq_right hp,row_phase_ramified u P hd,star_zero,add_zero,ite_eq_left hd]
        have h := hb.2
        simp only [ite_eq_right hj,add_zero] at h
        have hn : ‖centralNormalizedSlot η u P hs x w z‖≤800*(P.val.absNorm:ℝ)^(1/2:ℝ) := by
          dsimp only [centralNormalizedSlot]
          rw [hcorr]
          have hm := mul_le_mul_of_nonneg_left h hQ0.le
          have hpow : (P.val.absNorm:ℝ)*(P.val.absNorm:ℝ)^(-1:ℝ)=1 := by
            rw [Real.rpow_neg_one];exact mul_inv_cancel₀ hQ0.ne'
          have hp2 : (P.val.absNorm:ℝ)*(P.val.absNorm:ℝ)^(-(1/2:ℝ))=
              (P.val.absNorm:ℝ)^(1/2:ℝ) := by
            conv_lhs => lhs;rw [←Real.rpow_one (P.val.absNorm:ℝ)]
            rw [←Real.rpow_add hQ0];norm_num
          rw [←mul_assoc,hpow,one_mul] at hm
          rw [mul_left_comm (P.val.absNorm:ℝ) 800,hp2] at hm
          exact hm
        exact hn.trans (mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_nonneg hQ0.le _))
    · by_cases hj : 2≤multiplicity (primaryGenerator P.val) u.val
      · have hp : repeatedRowPrime u P := ⟨hd,hj⟩
        rw [centralRepeatedTerm,ite_eq_left hp,ite_eq_left hp]
        have h := hb.2
        rw [ite_eq_left hj] at h
        have hpow : (P.val.absNorm:ℝ)^(-(1/2:ℝ))≤(P.val.absNorm:ℝ)^(-w.re) := by
          apply Real.rpow_le_rpow_of_exponent_le hQ1
          rw [hw];linarith
        have hn : (P.val.absNorm:ℝ)^(-1:ℝ)*‖centralNormalizedSlot η u P hs x w z‖≤
            812*(P.val.absNorm:ℝ)^(-w.re) := by
          dsimp only [centralNormalizedSlot];rw [hcorr]
          nlinarith
        have hm := mul_le_mul_of_nonneg_left hn hQ0.le
        have hi : (P.val.absNorm:ℝ)*(P.val.absNorm:ℝ)^(-1:ℝ)=1 := by
          rw [Real.rpow_neg_one];exact mul_inv_cancel₀ hQ0.ne'
        have heq : (P.val.absNorm:ℝ)*(P.val.absNorm:ℝ)^(-w.re)=
            (P.val.absNorm:ℝ)^(1-w.re) := by
          conv_lhs => lhs;rw [←Real.rpow_one (P.val.absNorm:ℝ)]
          rw [←Real.rpow_add hQ0]; congr 1
        rw [←mul_assoc,hi,one_mul] at hm
        rw [mul_left_comm (P.val.absNorm:ℝ) 812,heq] at hm
        exact hm
      · have hp : ¬repeatedRowPrime u P := fun h=>hj h.2
        simp only [centralRepeatedTerm,ite_eq_right hp,norm_zero,le_refl]
  · have hb := actual_central_unramified_normalized η u P hs hd hη a e x w z hQ
      ha ha1 he he1 hx hw hz
    have hc : supportedCorrection η u P x w z=idealUnramifiedCorrection η u P x w z := by
      simp [supportedCorrection,hs,hd]
    have hp : ¬repeatedRowPrime u P := fun h=>hd h.1
    refine ⟨hc.symm ▸ hb.1,?_,?_⟩
    · simpa only [centralRegularError,ite_eq_right hp,centralNormalizedSlot,hc,ite_eq_right hd] using hb.2
    · simp only [centralRepeatedTerm,ite_eq_right hp,norm_zero,le_refl]
end SevenEighths.ProbeHighRowFamily
end

end OAI
