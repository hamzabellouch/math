import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootBruhat
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootBruhatResidues

namespace OAI

/-! The cubic-scale unit branch has trivial multiplier. This is a
consequence of the elementary cubic character, not a residue hypothesis. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRootBruhat_coprime {p : Eisenstein} (_hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p^3∣9*x*y-1) : IsCoprime p (3*y) := by
  obtain ⟨z,hz⟩ := hxy
  refine ⟨-(p^2*z),3*x,?_⟩
  linear_combination hz

lemma cubicThetaPrimeCubeRootBruhat_phase {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p^3∣9*x*y-1) : cubicSymbol (p^3) (3*y)=1 := by
  have hc := cubicThetaPrimeCubeRootBruhat_coprime hp x y hxy
  obtain ⟨u,hu⟩ := residue_isUnit_of_isCoprime hc
  have hp3 : cubicSymbol p (3*y)^3=1 := by
    rw [cubicSymbol_prime hp]
    apply cubicSymbolAtPrime_unit_cube hp
    rw [←hu]
    exact u.isUnit
  calc
    _ = cubicSymbol p (3*y)^3 := by
      rw [pow_succ,pow_two,cubicSymbol_mul_lower (mul_ne_zero hp.2.ne_zero hp.2.ne_zero) hp.2.ne_zero,
        cubicSymbol_mul_lower hp.2.ne_zero hp.2.ne_zero]
      ring
    _ = 1 := hp3

lemma cubicThetaPrimeCubeRootBruhat_kubota_one {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p^3∣9*x*y-1) :
    cubicThetaKubotaValue (cubicThetaPrimeCubeRootBruhat hp x y hxy)=1 := by
  rw [cubicThetaPrimeCubeRootBruhat_kubota,cubicThetaPrimeCubeRootBruhat_phase hp x y hxy]

lemma cubicThetaPrimeCubeRoot_nine_unit {p : Eisenstein} (hp : primaryPrime p) :
    IsUnit (Ideal.Quotient.mk (modulus (p^3)) 9) := by
  have hc : IsCoprime (p^3) (9:Eisenstein) := by
    convert (primary_coprime_three (cubicThetaPrimeCube_primary hp)).pow_right (n:=2) using 1
    norm_num
  obtain ⟨u,hu⟩ := residue_isUnit_of_isCoprime hc
  rw [←hu]
  exact u.isUnit

lemma cubicThetaPrimeCubeRootReciprocal_pair {p : Eisenstein} (hp : primaryPrime p)
    (r : Residues (p^3)) (hr : IsUnit r) :
    p^3∣9*residueRepresentative (p^3) (cubicThetaPrimeRootReciprocal (p^3) r)*
      residueRepresentative (p^3) r-1 := by
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change Ideal.Quotient.mk (modulus (p^3))
    (9*residueRepresentative (p^3) (cubicThetaPrimeRootReciprocal (p^3) r)*
      residueRepresentative (p^3) r-1)=0
  rw [map_sub,map_one,sub_eq_zero]
  simp only [map_mul,residueRepresentative_spec,cubicThetaPrimeRootReciprocal]
  calc
    _ = Ring.inverse (Ideal.Quotient.mk (modulus (p^3)) 9*r)*
        (Ideal.Quotient.mk (modulus (p^3)) 9*r) := by ring
    _ = 1 := Ring.inverse_mul_cancel _ ((cubicThetaPrimeCubeRoot_nine_unit hp).mul hr)

theorem cubicThetaPrimeCubeRootBruhat_section_one {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p^3∣9*x*y-1) (F : CubicThetaSection) (z : CubicThetaPoint) :
    F.val (cubicThetaPrimeCubeRootElement hp y •
      (cubicThetaPrimeCubeRootWeylElement hp • (cubicThetaPrimeCubeRootElement hp x • z)))=
      (cubicThetaInversionSection F).val z := by
  rw [cubicThetaPrimeCubeRootBruhat_section hp x y hxy F z,
    cubicThetaPrimeCubeRootBruhat_phase hp x y hxy,one_mul]

end CubicFirstMoment

end

end OAI
