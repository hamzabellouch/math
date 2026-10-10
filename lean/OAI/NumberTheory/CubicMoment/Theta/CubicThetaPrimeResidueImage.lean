import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCriticalFactors

namespace OAI

/-! Exact passage between the three actual prime-free residues and the
actual Fourier residues. It preserves the critical local image condition;
this does not assert that either family is in that image. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeResidueVector (p h : Eisenstein) : Fin 3 → ℂ :=
  ![cubicThetaArithmeticFourierResidue h (4/3),
    cubicThetaPrimeCriticalScale p*cubicThetaArithmeticFourierResidue (p*h) (4/3),
    (cubicThetaPrimeCriticalScale p)^2*cubicThetaArithmeticFourierResidue (p^2*h) (4/3)]

def cubicThetaPrimeFreeResidueVector (p h : Eisenstein) : Fin 3 → ℂ :=
  ![cubicThetaRegularizedPrimeFreeZero p h (4/3),
    cubicThetaPrimeCriticalScale p*cubicThetaRegularizedPrimeFreeTwo p h (4/3),
    (cubicThetaPrimeCriticalScale p)^2*cubicThetaRegularizedPrimeFreeOne p h (4/3)]

lemma cubicThetaPrimeResidueVector_zero {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : ¬p∣h) :
    cubicThetaPrimeResidueVector p h 0=cubicThetaPrimeFreeResidueVector p h 0+
      (cubicThetaPrimeAdditiveGauss p hp 1 h/(norm p:ℂ))*
        cubicThetaPrimeFreeResidueVector p h 1 := by
  have h0 : h≠0 := fun hz => hh (hz ▸ dvd_zero p)
  have he := cubicThetaRegularizedFrequency_primeFree_decomposition hp h hh
    (s:=(4/3:ℂ)) (by norm_num)
  rw [cubicThetaRegularizedFrequency_residue h0,
    cubicThetaPrimeFirstFactor_critical hp h (hp.2.coprime_iff_not_dvd.mpr hh)] at he
  simpa only [cubicThetaPrimeResidueVector,cubicThetaPrimeFreeResidueVector,
    Matrix.cons_val_zero,Matrix.cons_val_one,mul_assoc] using he

lemma cubicThetaPrimeResidueVector_one {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : ¬p∣h) :
    cubicThetaPrimeResidueVector p h 1=
      (cubicThetaPrimeAdditiveGauss p hp 2 h/(norm p:ℂ)^2)*
        cubicThetaPrimeFreeResidueVector p h 0+cubicThetaPrimeFreeResidueVector p h 1 := by
  have h0 : h≠0 := fun hz => hh (hz ▸ dvd_zero p)
  have he := cubicThetaRegularizedFrequency_primeFree_shift hp h hh
    (s:=(4/3:ℂ)) (by norm_num)
  rw [cubicThetaRegularizedFrequency_residue (mul_ne_zero hp.2.ne_zero h0)] at he
  have hs := congrArg (fun z : ℂ => cubicThetaPrimeCriticalScale p*z) he
  rw [mul_add,←mul_assoc,cubicThetaPrimeSecondFactor_critical hp h
    (hp.2.coprime_iff_not_dvd.mpr hh)] at hs
  exact hs

lemma cubicThetaPrimeResidueVector_two {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : h≠0) :
    cubicThetaPrimeResidueVector p h 2=cubicThetaPrimeDeterminant p (4/3)*
      cubicThetaPrimeFreeResidueVector p h 2 := by
  have hd := cubicThetaPrimeDeterminant_ne_zero hp (s:=(4/3:ℂ)) (by norm_num)
  change _=cubicThetaPrimeDeterminant p (4/3)*
    ((cubicThetaPrimeCriticalScale p)^2*
      (cubicThetaRegularizedFrequency (p^2*h) (4/3)/cubicThetaPrimeDeterminant p (4/3)))
  rw [cubicThetaRegularizedFrequency_residue (mul_ne_zero (pow_ne_zero 2 hp.2.ne_zero) hh)]
  field_simp
  rfl

lemma cubicThetaPrimeResidueVector_defect {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : ¬p∣h) :
    cubicThetaPrimeResidueVector p h 1-
        (cubicThetaPrimeAdditiveGauss p hp 2 h/(norm p:ℂ))*cubicThetaPrimeResidueVector p h 0=
      (1-(norm p:ℂ)⁻¹)*(cubicThetaPrimeFreeResidueVector p h 1-
        (cubicThetaPrimeAdditiveGauss p hp 2 h/(norm p:ℂ))*cubicThetaPrimeFreeResidueVector p h 0) := by
  rw [cubicThetaPrimeResidueVector_zero hp h hh,cubicThetaPrimeResidueVector_one hp h hh]
  have hq : (norm p:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (norm_pos_of_ne_zero hp.2.ne_zero).ne'
  have hg := cubicThetaPrimeAdditiveGauss_product hp h (hp.2.coprime_iff_not_dvd.mpr hh)
  field_simp
  linear_combination -(cubicThetaPrimeFreeResidueVector p h 1)*hg

theorem cubicThetaPrimeResidueImage_iff_free {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : ¬p∣h) :
    (∃ v : Fin 3 → ℂ, (cubicThetaPrimeCriticalMatrix p hp h).mulVec v=
      cubicThetaPrimeResidueVector p h) ↔
    (∃ v : Fin 3 → ℂ, (cubicThetaPrimeCriticalMatrix p hp h).mulVec v=
      cubicThetaPrimeFreeResidueVector p h) := by
  have hc := hp.2.coprime_iff_not_dvd.mpr hh
  rw [cubicThetaPrimeCriticalMatrix_range_iff hp h hc,
    cubicThetaPrimeCriticalMatrix_range_iff hp h hc]
  have hq1 : (norm p:ℂ)≠1 := by
    exact_mod_cast (ne_of_gt (cubicThetaPrimaryPrime_norm_gt_one hp))
  have hgap : 1-(norm p:ℂ)⁻¹≠0 := by
    intro hz
    exact (inv_ne_one.mpr hq1) (sub_eq_zero.mp hz).symm
  have hfirst : (cubicThetaPrimeResidueVector p h 1=
      (cubicThetaPrimeAdditiveGauss p hp 2 h/(norm p:ℂ))*cubicThetaPrimeResidueVector p h 0) ↔
      (cubicThetaPrimeFreeResidueVector p h 1=
      (cubicThetaPrimeAdditiveGauss p hp 2 h/(norm p:ℂ))*cubicThetaPrimeFreeResidueVector p h 0) := by
    rw [←sub_eq_zero,cubicThetaPrimeResidueVector_defect hp h hh]
    simp only [mul_eq_zero,hgap,false_or,sub_eq_zero]
  have hsecond : cubicThetaPrimeResidueVector p h 2=0 ↔ cubicThetaPrimeFreeResidueVector p h 2=0 := by
    rw [cubicThetaPrimeResidueVector_two hp h (fun hz => hh (hz ▸ dvd_zero p))]
    simp only [mul_eq_zero,cubicThetaPrimeDeterminant_ne_zero hp (s:=(4/3:ℂ)) (by norm_num),false_or]
  exact and_congr hfirst hsecond

end CubicFirstMoment

end

end OAI
