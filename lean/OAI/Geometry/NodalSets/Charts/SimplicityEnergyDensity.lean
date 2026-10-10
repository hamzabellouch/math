import OAI.Geometry.NodalSets.Elliptic.SimplicityRoundCoordinatePerturbation

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set
open scoped ContDiff
noncomputable section

def roundSimplicitySquare (u v : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) : ℝ :=
  roundCoordFactor x * ∑ i : Fin 4,
    (u x*Yau.coordPartial v x i-v x*Yau.coordPartial u x i)^2

lemma roundSimplicitySquare_nonneg (u v : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) :
    0 ≤ roundSimplicitySquare u v x :=
  mul_nonneg ((show (0:ℝ) ≤ 1 by norm_num).trans (roundCoordFactor_ge_one x))
    (Finset.sum_nonneg (fun i _ ↦ sq_nonneg _))

lemma roundSimplicitySquare_smooth (u v : Yau.Jets.Coord → ℝ)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) : ContDiff ℝ ∞ (roundSimplicitySquare u v) := by
  apply roundCoordFactor_smooth.mul
  apply ContDiff.sum
  intro i _
  exact ((hu.mul ((hv.fderiv_right (by simp)).clm_apply contDiff_const)).sub
    (hv.mul ((hu.fderiv_right (by simp)).clm_apply contDiff_const))).pow 2

lemma roundSimplicitySquare_expand (u v : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord) :
    roundSimplicitySquare u v x =
      u x^2*Yau.pairing v (roundCoordGradient v) x +
      v x^2*Yau.pairing u (roundCoordGradient u) x -
      2*u x*v x*Yau.pairing v (roundCoordGradient u) x := by
  unfold roundSimplicitySquare Yau.pairing roundCoordGradient Yau.coordPartial
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma round_pairing_mul_square (u v zeta : Yau.Jets.Coord → ℝ) (x : Yau.Jets.Coord)
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) :
    Yau.pairing (fun y ↦ u y*v y^2) (fun y i ↦ zeta y*roundCoordGradient u y i) x =
      zeta x*(v x^2*Yau.pairing u (roundCoordGradient u) x +
        2*u x*v x*Yau.pairing v (roundCoordGradient u) x) := by
  have hd (i : Fin 4) : Yau.coordPartial (fun y ↦ u y*v y^2) x i =
      Yau.coordPartial u x i*v x^2+2*u x*v x*Yau.coordPartial v x i := by
    unfold Yau.coordPartial
    simp only [pow_two]
    have hv2 : DifferentiableAt ℝ (fun y ↦ v y*v y) x := hv.mul hv
    rw [fderiv_fun_mul hu hv2,fderiv_fun_mul hv hv]
    simp only [add_apply,smul_apply,smul_eq_mul]
    ring
  unfold Yau.pairing
  simp only [hd,Finset.mul_sum,mul_add]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem round_simplicity_energy_density (u v zeta : Yau.Jets.Coord → ℝ)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (hz : ContDiff ℝ ∞ zeta)
    (lam : ℝ) (hlam : lam ≠ 0) (x : Yau.Jets.Coord) :
    zeta x*u x^2*Yau.pairing v (roundCoordGradient v) x -
      lam*simplicityDensityPerturbation roundCoordDensity u zeta (roundCoordGradient u) lam x*v x^2 =
      zeta x*roundSimplicitySquare u v x +
        Yau.weightedDiv roundCoordDensity
          (fun y i ↦ (u y*v y^2)*(zeta y*roundCoordGradient u y i)) x := by
  have hV := roundCoordGradient_smooth u hu
  have hdiv := Yau.weightedDiv_mul (gamma := roundCoordDensity) (u := fun y ↦ u y*v y^2)
    (V := fun y i ↦ zeta y*roundCoordGradient u y i) (x := x)
    (roundCoordDensity_smooth.differentiable (by simp) x) (roundCoordDensity_pos x).ne'
    ((hu.mul (hv.pow 2)).differentiable (by simp) x)
    (fun i ↦ (hz.mul ((contDiff_pi.mp hV) i)).differentiable (by simp) x)
  rw [hdiv,round_pairing_mul_square u v zeta x
    (hu.differentiable (by simp) x) (hv.differentiable (by simp) x),roundSimplicitySquare_expand]
  unfold simplicityDensityPerturbation
  field_simp
  ring

end
end Yau.Target

end OAI
