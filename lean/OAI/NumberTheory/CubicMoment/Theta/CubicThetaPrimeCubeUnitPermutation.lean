import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeReductionResidue

namespace OAI

/-! The exact finite unit permutation produced by triangularization:
the residue of the new period-three translation is (9n)^{-1}. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeCubeNineUnit {p : Eisenstein} (hp : primaryPrime p) (k : Fin 3) :
    (Residues (p^(3-k.val)))ˣ := by
  have h9 : IsCoprime (p^(3-k.val)) (9:Eisenstein) := by
    convert (primary_coprime_three (cubicThetaPrimeCubeReduction_primary hp k)).pow_right
      (n := 2) using 1
    norm_num
  exact (residue_isUnit_of_isCoprime h9).unit

lemma cubicThetaPrimeCubeNineUnit_value {p : Eisenstein} (hp : primaryPrime p) (k : Fin 3) :
    (cubicThetaPrimeCubeNineUnit hp k : Residues (p^(3-k.val)))=
      Ideal.Quotient.mk (modulus (p^(3-k.val))) 9 := IsUnit.unit_spec _

def cubicThetaPrimeCubeUnitPermutation {p : Eisenstein} (hp : primaryPrime p) (k : Fin 3) :
    (Residues (p^(3-k.val)))ˣ ≃ (Residues (p^(3-k.val)))ˣ where
  toFun u := (cubicThetaPrimeCubeNineUnit hp k*u)⁻¹
  invFun v := (cubicThetaPrimeCubeNineUnit hp k)⁻¹*v⁻¹
  left_inv u := by simp
  right_inv v := by simp

lemma cubicThetaPrimeCubeUnitRepresentative_not_dvd {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (u : (Residues (p^(3-k.val)))ˣ) :
    ¬p∣residueRepresentative (p^(3-k.val)) (u : Residues (p^(3-k.val))) := by
  apply hp.2.coprime_iff_not_dvd.mp
  have hpu : IsCoprime (p^(3-k.val))
      (residueRepresentative (p^(3-k.val)) (u : Residues (p^(3-k.val)))) := by
    apply isCoprime_of_residue_isUnit
    rw [residueRepresentative_spec]
    exact u.isUnit
  exact hpu.of_isCoprime_of_dvd_left (dvd_pow_self p (by have := k.isLt; omega))

theorem cubicThetaPrimeCubeUnitTranslation_residue {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (u : (Residues (p^(3-k.val)))ˣ) :
    Ideal.Quotient.mk (modulus (p^(3-k.val)))
      (cubicThetaPrimeCubeReductionTranslation hp k
        (residueRepresentative (p^(3-k.val)) (u : Residues (p^(3-k.val))))
        (cubicThetaPrimeCubeUnitRepresentative_not_dvd hp k u))=
      (cubicThetaPrimeCubeUnitPermutation hp k u : Residues (p^(3-k.val))) := by
  rw [cubicThetaPrimeCubeReductionTranslation_residue]
  have he : cubicThetaPrimeCubeReductionTranslationUnit hp k
      (residueRepresentative (p^(3-k.val)) (u : Residues (p^(3-k.val))))
      (cubicThetaPrimeCubeUnitRepresentative_not_dvd hp k u)=cubicThetaPrimeCubeNineUnit hp k*u := by
    apply Units.ext
    change Ideal.Quotient.mk (modulus (p^(3-k.val)))
      (9*residueRepresentative (p^(3-k.val)) (u : Residues (p^(3-k.val))))=_
    rw [map_mul,residueRepresentative_spec,Units.val_mul,cubicThetaPrimeCubeNineUnit_value]
  rw [he]
  rfl

end CubicFirstMoment

end

end OAI
