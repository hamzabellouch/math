import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeReductionPhase

namespace OAI

/-! The translation selected by the actual row completion is the inverse
of 9n modulo its prime power. Thus its choice agrees with finite Fourier
reindexing and with the original period-three lattice. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeCubeReductionTranslation {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (n : Eisenstein) (hn : ¬p∣n) : Eisenstein :=
  (cubicThetaPrimeCubeReduction hp k n hn).val 0 1/3

lemma cubicThetaPrimeCubeReductionTranslation_three {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (n : Eisenstein) (hn : ¬p∣n) :
    3*cubicThetaPrimeCubeReductionTranslation hp k n hn=
      (cubicThetaPrimeCubeReduction hp k n hn).val 0 1 := by
  apply EuclideanDomain.mul_div_cancel' (by norm_num : (3:Eisenstein)≠0)
  exact (cubicThetaPrincipalGroup_offDiagonal (cubicThetaPrimeCubeReduction hp k n hn)).1

lemma cubicThetaPrimeCubeReductionTranslation_congruence {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (n : Eisenstein) (hn : ¬p∣n) :
    p^(3-k.val) ∣ 9*n*cubicThetaPrimeCubeReductionTranslation hp k n hn-1 := by
  have he := cubicThetaPrimeCubeReduction_determinant hp k n hn
  rw [←cubicThetaPrimeCubeReductionTranslation_three hp k n hn] at he
  refine ⟨-(cubicThetaPrimeCubeReduction hp k n hn).val 0 0,?_⟩
  linear_combination he

def cubicThetaPrimeCubeReductionTranslationUnit {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (n : Eisenstein) (hn : ¬p∣n) : (Residues (p^(3-k.val)))ˣ := by
  have h9 : IsCoprime (p^(3-k.val)) (9:Eisenstein) := by
    convert (primary_coprime_three (cubicThetaPrimeCubeReduction_primary hp k)).pow_right
      (n := 2) using 1
    norm_num
  exact (residue_isUnit_of_isCoprime
    (h9.mul_right ((hp.2.coprime_iff_not_dvd.mpr hn).pow_left))).unit

theorem cubicThetaPrimeCubeReductionTranslation_residue {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (n : Eisenstein) (hn : ¬p∣n) :
    Ideal.Quotient.mk (modulus (p^(3-k.val)))
      (cubicThetaPrimeCubeReductionTranslation hp k n hn)=
        ((cubicThetaPrimeCubeReductionTranslationUnit hp k n hn)⁻¹ :
          (Residues (p^(3-k.val)))ˣ) := by
  let u := cubicThetaPrimeCubeReductionTranslationUnit hp k n hn
  have hu : (u : Residues (p^(3-k.val)))=
      Ideal.Quotient.mk (modulus (p^(3-k.val))) (9*n) := IsUnit.unit_spec _
  apply u.eq_inv_of_mul_eq_one_left
  rw [hu,←map_mul]
  exact (residue_eq_of_dvd_sub
    (cubicThetaPrimeCubeReductionTranslation_congruence hp k n hn)).trans (map_one _)

end CubicFirstMoment

end

end OAI
