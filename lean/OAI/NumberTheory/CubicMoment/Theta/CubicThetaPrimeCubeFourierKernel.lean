import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeGauss
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeResidueStep

namespace OAI

/-! The unit-branch Fourier kernels, with their actual zero extension.
The passage from units to all residues is valid precisely for the two
positive cubic powers occurring in the Hecke correspondence. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeCharacter_representative {p : Eisenstein}
    (hp : primaryPrime p) (k : Fin 3) (y : Residues (p^(3-k.val))) :
    cubicSymbol p (residueRepresentative (p^(3-k.val)) y)=
      cubicResidueChar p hp (residueReduction (cubicThetaPrimeCubePrimeDivisor p k) y) := by
  have he := congrArg (residueReduction (cubicThetaPrimeCubePrimeDivisor p k))
    (residueRepresentative_spec (p^(3-k.val)) y)
  rw [residueReduction_mk] at he
  rw [←he,cubicResidueChar_mk,cubicSymbol_prime hp]

lemma cubicThetaPrimeCubeCharacter_nonunit {p : Eisenstein}
    (hp : primaryPrime p) (k : Fin 3) (hk : k.val≠0)
    (m : Eisenstein) :
    (cubicResidueChar p hp (residueReduction (cubicThetaPrimeCubePrimeDivisor p k)
      (Ideal.Quotient.mk (modulus (p^(3-k.val))) (p*m))))^k.val=0 := by
  let : (modulus p).IsPrime := (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  rw [residueReduction_mk,map_mul]
  have hz : Ideal.Quotient.mk (modulus p) p=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (dvd_refl p))
  rw [hz,zero_mul,MulChar.map_zero,zero_pow hk]

lemma cubicThetaPrimeCubeGauss_units {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (hk : k.val≠0) (h : Eisenstein) :
    cubicThetaPrimeCubeFiniteGauss hp k h=
      ∑' u : (Residues (p^(3-k.val)))ˣ,
        (cubicResidueChar p hp (residueReduction (cubicThetaPrimeCubePrimeDivisor p k) u))^k.val*
          residueFourierChar (p^(3-k.val)) (pow_ne_zero _ hp.2.ne_zero)
            (Ideal.Quotient.mk (modulus (p^(3-k.val))) h*u) := by
  let f : Residues (p^(3-k.val)) → ℂ := fun y =>
    (cubicResidueChar p hp (residueReduction (cubicThetaPrimeCubePrimeDivisor p k) y))^k.val*
      residueFourierChar (p^(3-k.val)) (pow_ne_zero _ hp.2.ne_zero)
        (Ideal.Quotient.mk (modulus (p^(3-k.val))) h*y)
  have hs := cubicThetaPrimeCubeResidueSum_split hp (⟨2-k.val,by omega⟩ : Fin 3)
  have he : 2-k.val+1=3-k.val := by have := k.isLt; omega
  dsimp only at hs
  rw [he] at hs
  have ht := hs f
  have hz (r : Residues (p^(2-k.val))) :
      f (Ideal.Quotient.mk (modulus (p^(3-k.val)))
        (p*residueRepresentative (p^(2-k.val)) r))=0 := by
    dsimp only [f]
    rw [cubicThetaPrimeCubeCharacter_nonunit hp k hk,zero_mul]
  simp_rw [hz] at ht
  simpa only [f,cubicThetaPrimeCubeFiniteGauss,tsum_zero,add_zero] using ht

def cubicThetaPrimeCubeUnitFourier {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (h : Eisenstein) : ℂ :=
  ∑' u : (Residues (p^(3-k.val)))ˣ,
    (cubicSymbol p (3*residueRepresentative (p^(3-k.val)) (u : Residues (p^(3-k.val)))))^k.val*
      residueFourierChar (p^(3-k.val)) (pow_ne_zero _ hp.2.ne_zero)
        (Ideal.Quotient.mk (modulus (p^(3-k.val))) h*u)

theorem cubicThetaPrimeCubeUnitFourier_eq {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (hk : k.val≠0) (h : Eisenstein) :
    cubicThetaPrimeCubeUnitFourier hp k h=
      (cubicSymbol p 3)^k.val*cubicThetaPrimeCubeFiniteGauss hp k h := by
  unfold cubicThetaPrimeCubeUnitFourier
  rw [cubicThetaPrimeCubeGauss_units hp k hk,←tsum_mul_left]
  apply tsum_congr
  intro u
  rw [cubicSymbol_mul_upper hp.1,mul_pow,cubicThetaPrimeCubeCharacter_representative hp]
  ring

theorem cubicThetaPrimeCubeUnitFourier_zero {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (hk : k.val≠0) (h : Eisenstein) (hh : ¬p^(2-k.val)∣h) :
    cubicThetaPrimeCubeUnitFourier hp k h=0 := by
  rw [cubicThetaPrimeCubeUnitFourier_eq hp k hk,
    cubicThetaPrimeCubeFiniteGauss_zero hp k h hh,mul_zero]

theorem cubicThetaPrimeCubeUnitFourier_reduction {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (hk : k.val≠0) (h : Eisenstein) :
    cubicThetaPrimeCubeUnitFourier hp k (p^(2-k.val)*h)=
      (cubicSymbol p 3)^k.val*(norm (p^(2-k.val)):ℂ)*cubicThetaPrimeFourier p hp k.val h := by
  rw [cubicThetaPrimeCubeUnitFourier_eq hp k hk,cubicThetaPrimeCubeFiniteGauss_reduction]
  ring

end CubicFirstMoment

end

end OAI
