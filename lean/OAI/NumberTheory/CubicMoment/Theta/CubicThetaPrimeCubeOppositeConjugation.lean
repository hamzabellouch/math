import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeBranchPeriodicity

namespace OAI

/-! The complementary chart becomes the inverse dilation. The actual
integral conjugating matrix has exactly the Weyl representative's multiplier. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeWeyl_division {p : Eisenstein} (hp : primaryPrime p) :
    p^3*(cubicThetaPrimeCubeWeylDenominator hp/p^3)=cubicThetaPrimeCubeWeylDenominator hp :=
  EuclideanDomain.mul_div_cancel' (pow_ne_zero 3 hp.2.ne_zero)
    (cubicThetaPrimeCubeWeylDenominator_dvd hp)

def cubicThetaPrimeCubeOppositeMatrix {p : Eisenstein} (hp : primaryPrime p) : SL(2,Eisenstein) where
  val := !![p^3*(cubicThetaPrimeCubeWeyl hp).val 0 0,(cubicThetaPrimeCubeWeyl hp).val 0 1;
    3,cubicThetaPrimeCubeWeylDenominator hp/p^3]
  property := by
    have he := cubicThetaPrincipalGroup_det (cubicThetaPrimeCubeWeyl hp)
    rw [cubicThetaPrimeCubeWeyl_c,cubicThetaPrimeCubeWeyl_d] at he
    rw [Matrix.det_fin_two_of]
    linear_combination he+(cubicThetaPrimeCubeWeyl hp).val 0 0*
      (cubicThetaPrimeCubeWeyl_division hp)

lemma cubicThetaPrimeCubeOppositeMatrix_mem {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeCubeOppositeMatrix hp∈cubicThetaPrincipalGroup := by
  have ha := (cubicThetaPrincipalGroup_diagonal_primary (cubicThetaPrimeCubeWeyl hp)).1
  have hb := (cubicThetaPrincipalGroup_offDiagonal (cubicThetaPrimeCubeWeyl hp)).1
  have hd : primary (cubicThetaPrimeCubeWeylDenominator hp/p^3) :=
    primary_of_mul (cubicThetaPrimeCube_primary hp) (by
      rw [cubicThetaPrimeCubeWeyl_division]
      exact cubicThetaPrimeCubeWeylDenominator_primary hp)
  exact (cubicThetaPrincipalGroup_mem_iff _).mpr
    ⟨primary_mul (cubicThetaPrimeCube_primary hp) ha,hb,dvd_refl _,hd⟩

def cubicThetaPrimeCubeOpposite {p : Eisenstein} (hp : primaryPrime p) : cubicThetaPrincipalGroup :=
  ⟨cubicThetaPrimeCubeOppositeMatrix hp,cubicThetaPrimeCubeOppositeMatrix_mem hp⟩

lemma cubicThetaPrimeCubeOpposite_kubota {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaKubotaValue (cubicThetaPrimeCubeOpposite hp)=
      cubicThetaKubotaValue (cubicThetaPrimeCubeWeyl hp) := by
  have ha := (cubicThetaPrincipalGroup_diagonal_primary (cubicThetaPrimeCubeWeyl hp)).1
  rw [cubicThetaKubotaValue_eq_symbol,cubicThetaKubotaValue_eq_symbol,cubicThetaPrimeCubeWeyl_c]
  change cubicSymbol (p^3*(cubicThetaPrimeCubeWeyl hp).val 0 0) 3=_
  rw [cubicSymbol_mul_lower (pow_ne_zero 3 hp.2.ne_zero) (primary_ne_zero ha),
    cubicThetaSymbol_prime_pow hp,cubicSymbol_cube_of_isCoprime hp.1 3
      (primary_coprime_three hp.1),one_mul]

theorem cubicThetaPrimeCubeOpposite_intertwines {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero)*
      cubicThetaPrincipalComplex (cubicThetaPrimeCubeWeyl hp)=
    cubicThetaPrincipalComplex (cubicThetaPrimeCubeOpposite hp)*
      (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero))⁻¹ := by
  let q := cubicThetaPrimeSquareRoot (p^3)
  have hq : q≠0 := cubicThetaPrimeSquareRoot_ne_zero (pow_ne_zero 3 hp.2.ne_zero)
  have hs : q^2=(p:ℂ)^3 := (cubicThetaPrimeSquareRoot_sq (p^3)).trans
    (map_pow (eisensteinRing.subtype : Eisenstein →+* ℂ) p 3)
  have hd : (p:ℂ)^3*((cubicThetaPrimeCubeWeylDenominator hp/p^3:Eisenstein):ℂ)=
      (cubicThetaPrimeCubeWeylDenominator hp:Eisenstein) := by
    have h := congrArg (fun z : Eisenstein => (z:ℂ)) (cubicThetaPrimeCubeWeyl_division hp)
    push_cast at h
    exact h
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply,Fin.sum_univ_two,cubicThetaPrimeDilation,
      cubicThetaPrincipalComplex_apply,
      cubicThetaPrimeCubeOpposite,cubicThetaPrimeCubeOppositeMatrix]
    change q*((cubicThetaPrimeCubeWeyl hp).val 0 0:Eisenstein)=_
    change q*((cubicThetaPrimeCubeWeyl hp).val 0 0:Eisenstein)=
      ((p:ℂ)^3*((cubicThetaPrimeCubeWeyl hp).val 0 0:Eisenstein))*q⁻¹
    field_simp
    linear_combination ((cubicThetaPrimeCubeWeyl hp).val 0 0:Eisenstein)*hs
  · simp [Matrix.mul_apply,Fin.sum_univ_two,cubicThetaPrimeDilation,
      cubicThetaPrincipalComplex_apply,
      cubicThetaPrimeCubeOpposite,cubicThetaPrimeCubeOppositeMatrix,mul_comm]
  · simp [Matrix.mul_apply,Fin.sum_univ_two,cubicThetaPrimeDilation,
      cubicThetaPrincipalComplex_apply,
      cubicThetaPrimeCubeOpposite,cubicThetaPrimeCubeOppositeMatrix,cubicThetaPrimeCubeWeyl_c,mul_comm]
  · simp [Matrix.mul_apply,Fin.sum_univ_two,cubicThetaPrimeDilation,
      cubicThetaPrincipalComplex_apply,
      cubicThetaPrimeCubeOpposite,cubicThetaPrimeCubeOppositeMatrix,cubicThetaPrimeCubeWeyl_d]
    change q⁻¹*(cubicThetaPrimeCubeWeylDenominator hp:Eisenstein)=_
    field_simp
    linear_combination -hd-((cubicThetaPrimeCubeWeylDenominator hp/p^3:Eisenstein):ℂ)*hs

end CubicFirstMoment

end

end OAI
