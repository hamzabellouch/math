import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeFirstPeriodization

namespace OAI

/-! Zero extension and the zero-frequency sum for the first character
branch, stated on its actual full residue ring. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeFirstCoefficient_nonunit {p : Eisenstein} (hp : primaryPrime p)
    (m : Eisenstein) :
    cubicSymbol p (3*residueRepresentative (p^2)
      (Ideal.Quotient.mk (modulus (p^2)) (p*m)))=0 := by
  let : (modulus p).IsPrime := (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  have hr : p∣residueRepresentative (p^2)
      (Ideal.Quotient.mk (modulus (p^2)) (p*m)) :=
    cubicThetaPrimeCubeResidueStep_divisible (⟨1,by decide⟩:Fin 3) (dvd_mul_right p m)
  have hz : Ideal.Quotient.mk (modulus p) (3*residueRepresentative (p^2)
      (Ideal.Quotient.mk (modulus (p^2)) (p*m)))=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (dvd_mul_of_dvd_right hr 3))
  rw [cubicSymbol_prime hp,←cubicResidueChar_mk p hp,hz,MulChar.map_zero]

lemma cubicThetaPrimeCubeFirstCoefficient_sum {p : Eisenstein} (hp : primaryPrime p) :
    (∑' r : Residues (p^2),cubicSymbol p (3*residueRepresentative (p^2) r))=0 := by
  have hu := cubicThetaPrimeCubeUnitFourier_zeroFrequency hp 1 (by decide)
  rw [cubicThetaPrimeCubeUnitFourier_zero_eq] at hu
  have hu' : (∑' u : (Residues (p^2))ˣ,
      cubicSymbol p (3*residueRepresentative (p^2) (u:Residues (p^2))))=0 := by
    simpa only [Fin.val_one,Nat.reduceSub,pow_one] using hu
  rw [cubicThetaPrimeCubeResidueSum_two hp]
  simp_rw [cubicThetaPrimeCubeFirstCoefficient_nonunit hp]
  rw [hu',tsum_zero,add_zero]

lemma cubicThetaPrimeCubeFirstPeriodization_units {p : Eisenstein} (hp : primaryPrime p)
    (f : ℂ → ℂ) (z : ℂ) :
    cubicThetaPrimeCubeFirstPeriodization p f z=
      ∑' u : (Residues (p^2))ˣ,
        cubicThetaPrimeCubeFirstTerm p f (residueRepresentative (p^2) (u:Residues (p^2))) z := by
  unfold cubicThetaPrimeCubeFirstPeriodization
  rw [cubicThetaPrimeCubeResidueSum_two hp]
  have hz (r : Residues p) :
      cubicThetaPrimeCubeFirstTerm p f (residueRepresentative (p^2)
        (Ideal.Quotient.mk (modulus (p^2)) (p*residueRepresentative p r))) z=0 := by
    unfold cubicThetaPrimeCubeFirstTerm
    rw [cubicThetaPrimeCubeFirstCoefficient_nonunit hp,zero_mul]
  simp_rw [hz]
  rw [tsum_zero,add_zero]

end CubicFirstMoment

end

end OAI
