import OAI.NumberTheory.CubicMoment.Theta.CubicThetaActualProjection

namespace OAI

/-! The finite primary projector gives an explicit dual coefficient
family, with absolute convergence and its actual constant term. -/
noncomputable section
open scoped BigOperators MatrixGroups
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

def cubicThetaProjectedCoefficient (g : SL(2,Eisenstein)) (hc : primary (g 1 0))
    (k : Eisenstein) : ℂ :=
  (∑ j : Fin 3, omega^j.val*star (cubicThetaProjectedCuspMultiplier g hc j)*
    star (cubicThetaActualCuspCoefficient (cubicThetaProjectedCuspType g j) (-k)))/3

def cubicThetaProjectedConstant (g : SL(2,Eisenstein)) (hc : primary (g 1 0)) : ℂ :=
  (∑ j : Fin 3, omega^j.val*star (cubicThetaProjectedCuspMultiplier g hc j)*
    star (cubicThetaActualCuspConstant (cubicThetaProjectedCuspType g j)))/3

lemma cubicThetaProjectedCuspMultiplier_norm (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (j : Fin 3) :
    ‖cubicThetaProjectedCuspMultiplier g hc j‖=1 := cubicThetaKubotaValue_norm _

lemma cubicThetaProjectedCoefficient_bound (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (k : Eisenstein) :
    ‖cubicThetaProjectedCoefficient g hc k‖≤243 := by
  have hω : ‖omega‖=1 := by
    have he := cubicTheta_unit_norm
      (Units.mkOfMulEqOne omegaE (omegaE^2) (by rw [mul_comm,←pow_succ,omegaE_cube]))
    exact he
  have hterm (j : Fin 3) :
      ‖omega^j.val*star (cubicThetaProjectedCuspMultiplier g hc j)*
        star (cubicThetaActualCuspCoefficient (cubicThetaProjectedCuspType g j) (-k))‖≤243 := by
    simp only [norm_mul,norm_pow,norm_star,hω,one_pow,
      cubicThetaProjectedCuspMultiplier_norm,one_mul]
    exact cubicThetaActualCuspCoefficient_bound _ _
  rw [cubicThetaProjectedCoefficient,norm_div,Complex.norm_ofNat]
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<3)).mpr
  calc
    _ ≤ ∑ j : Fin 3, ‖omega^j.val*star (cubicThetaProjectedCuspMultiplier g hc j)*
        star (cubicThetaActualCuspCoefficient (cubicThetaProjectedCuspType g j) (-k))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j : Fin 3, (243:ℝ) := Finset.sum_le_sum (fun j _ => hterm j)
    _ = _ := by norm_num

lemma cubicThetaNonconstant_three (a : Fin 3→Eisenstein→ℂ) (w : Fin 3→ℂ)
    (z : ℂ) (v : ℝ) (hs : ∀ j, Summable (cubicThetaSeriesTerm (a j) z v)) :
    cubicThetaNonconstant (fun k => (∑ j : Fin 3,w j*a j k)/3) (z,v)=
      (∑ j : Fin 3,w j*cubicThetaNonconstant (a j) (z,v))/3 := by
  have ht (k : Eisenstein) :
      cubicThetaSeriesTerm (fun k => (∑ j : Fin 3,w j*a j k)/3) z v k=
        (∑ j : Fin 3,w j*cubicThetaSeriesTerm (a j) z v k)/3 := by
    by_cases hk : k=0
    · simp [cubicThetaSeriesTerm,hk]
    · simp only [cubicThetaSeriesTerm,ite_eq_right hk]
      rw [div_mul_eq_mul_div,div_mul_eq_mul_div]
      simp_rw [Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring
  unfold cubicThetaNonconstant
  simp_rw [ht]
  rw [tsum_div_const,Summable.tsum_finsetSum (fun j _ => (hs j).mul_left (w j))]
  simp_rw [tsum_mul_left]

lemma cubicThetaProjectedCoefficient_series (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (z : ℂ) {v : ℝ} (hv : 0<v) :
    cubicThetaNonconstant (cubicThetaProjectedCoefficient g hc) (z,v)=
      (∑ j : Fin 3,omega^j.val*star (cubicThetaProjectedCuspMultiplier g hc j)*
        cubicThetaNonconstant
          (fun k => star (cubicThetaActualCuspCoefficient (cubicThetaProjectedCuspType g j) (-k)))
          (z,v))/3 := by
  apply cubicThetaNonconstant_three
  intro j
  apply cubicThetaSeries_summable (by norm_num : (0:ℝ)≤243) _ hv z
  intro k hk
  rw [norm_star]
  exact (cubicThetaActualCuspCoefficient_bound _ _).trans
    (le_mul_of_one_le_right (by norm_num) (one_le_norm hk))

theorem cubicThetaNormalizedPrimaryProjection_expansion (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (p : CubicThetaPoint) :
    cubicThetaNonconstant cubicThetaSelectedCoefficient (g • p).val=
      cubicThetaProjectedConstant g hc*((p.val.2^(2/3:ℝ):ℝ):ℂ)+
        cubicThetaNonconstant (cubicThetaProjectedCoefficient g hc)
          (p.val.1+(g 1 1:ℂ),p.val.2) := by
  have hp : (cubicThetaFullTranslation (g 1 1) • p).val=
      (p.val.1+(g 1 1:ℂ),p.val.2) := by
    rw [cubicThetaFullPointAction_apply,cubicThetaFullTranslation_complex,cubicThetaMobius_translation]
  rw [cubicThetaNormalizedPrimaryProjection_cusps g hc p,hp,
    cubicThetaProjectedCoefficient_series g hc _ p.property]
  have ht (j : Fin 3) : omega^j.val*star (cubicThetaProjectedCuspMultiplier g hc j*
      cubicThetaCuspExpansion (cubicThetaProjectedCuspType g j)
        (p.val.1+(g 1 1:ℂ),p.val.2))=
      omega^j.val*star (cubicThetaProjectedCuspMultiplier g hc j)*
        star (cubicThetaActualCuspConstant (cubicThetaProjectedCuspType g j))*
          ((p.val.2^(2/3:ℝ):ℝ):ℂ)+
      omega^j.val*star (cubicThetaProjectedCuspMultiplier g hc j)*
        cubicThetaNonconstant
          (fun k => star (cubicThetaActualCuspCoefficient (cubicThetaProjectedCuspType g j) (-k)))
          (p.val.1+(g 1 1:ℂ),p.val.2) := by
    rw [star_mul,cubicThetaCuspExpansion_conjugate]
    dsimp only [Prod.snd]
    ring
  simp_rw [ht]
  rw [Finset.sum_add_distrib,add_div]
  congr 1
  rw [←Finset.sum_mul]
  unfold cubicThetaProjectedConstant
  ring

end CubicFirstMoment

end

end OAI
