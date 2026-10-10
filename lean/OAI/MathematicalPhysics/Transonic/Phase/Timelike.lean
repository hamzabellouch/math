import OAI.MathematicalPhysics.Transonic.Phase.Coordinates

namespace OAI

section
noncomputable section
namespace SepticProfile
open Set Filter
open scoped ContDiff Topology BigOperators

def minkowskiSquare (s : ℝ → PhysicalSpace → ℝ) (t : ℝ) (X : PhysicalSpace) : ℝ :=
  (deriv (fun q => s q X) t)^2-
    ∑ j : Fin 4, (deriv (fun r => s t (coordinateLine X j r)) 0)^2

lemma GlobalProfile.radialH_integrand_factor (P : GlobalProfile) (X : PhysicalSpace) (t : ℝ) :
    P.b*P.radialH (radiusSq X/t^2)*P.radialIntegrand (radiusSq X/t^2)=
      P.A (radius X/t)*P.g (radiusSq X/t^2) := by
  have hy : (radius X/t)^2=radiusSq X/t^2 := by rw [div_pow,radius_sq]
  rw [P.A_eq,P.H_radial,hy,GlobalProfile.radialIntegrand,GlobalProfile.velocity,hy]
  have he : 1-(radius X/t)*(radius X/t*P.g (radiusSq X/t^2))=
      1-(radiusSq X/t^2)*P.g (radiusSq X/t^2) := by rw [← mul_assoc,← sq,hy]
  rw [he]
  ring

lemma GlobalProfile.s0_coordinate_derivative_simple (P : GlobalProfile) {t : ℝ}
    (ht : 0<t) (X : PhysicalSpace) (j : Fin 4) :
    HasDerivAt (fun r => P.s0 t (coordinateLine X j r))
      (t^(-P.beta)*P.A (radius X/t)*P.g (radiusSq X/t^2)*X j/t) 0 := by
  have hd := P.s0_coordinate_derivative (t:=t) X j
  rw [P.radialH_integrand_factor] at hd
  have hpow : t^(-P.b)=t*t^(-P.beta) := by
    have he : -P.b=1+(-P.beta) := by unfold GlobalProfile.b; ring
    rw [he,Real.rpow_add ht,Real.rpow_one]
  rw [hpow] at hd
  convert hd using 1
  field_simp

lemma sum_coordinate_sq (X : PhysicalSpace) (c : ℝ) :
    (∑ j : Fin 4, (c*X j)^2)=c^2*radiusSq X := by
  simp_rw [mul_pow]
  rw [← Finset.mul_sum]
  rfl

lemma GlobalProfile.s0_minkowskiSquare (P : GlobalProfile) {t : ℝ} (ht : 0<t)
    (X : PhysicalSpace) :
    minkowskiSquare P.s0 t X=(t^(-P.beta))^2*P.M0 (radius X/t) := by
  unfold minkowskiSquare
  rw [(P.s0_time_derivative ht X).deriv]
  simp_rw [(P.s0_coordinate_derivative_simple ht X _).deriv]
  have he (j : Fin 4) : t^(-P.beta)*P.A (radius X/t)*P.g (radiusSq X/t^2)*X j/t=
      (t^(-P.beta)*P.A (radius X/t)*P.g (radiusSq X/t^2)/t)*X j := by ring
  simp_rw [he]
  rw [sum_coordinate_sq,P.M0_factor,GlobalProfile.velocity]
  simp only [div_pow,radius_sq]
  field_simp
  simp only [radius_sq]

lemma GlobalProfile.s0_timelike (P : GlobalProfile) {t : ℝ} (ht : 0<t)
    (X : PhysicalSpace) : 0 < minkowskiSquare P.s0 t X := by
  rw [P.s0_minkowskiSquare ht X]
  exact mul_pos (sq_pos_of_pos (Real.rpow_pos_of_pos ht _)) (P.M0_pos _)

lemma radiusSq_smooth : ContDiff ℝ ∞ radiusSq := by
  apply ContDiff.sum
  intro i hi
  exact (contDiff_apply ℝ ℝ i).pow 2

lemma GlobalProfile.s0_smooth (P : GlobalProfile) :
    ContDiffOn ℝ ∞ (fun z : ℝ×PhysicalSpace => P.s0 z.1 z.2) {z | 0<z.1} := by
  have hr : ContDiff ℝ ∞ (fun z : ℝ×PhysicalSpace => radiusSq z.2) :=
    radiusSq_smooth.comp contDiff_snd
  have harg : ContDiffOn ℝ ∞ (fun z : ℝ×PhysicalSpace => radiusSq z.2/z.1^2) {z | 0<z.1} :=
    hr.contDiffOn.div (contDiff_fst.pow 2).contDiffOn (fun z hz => pow_ne_zero 2 (ne_of_gt hz))
  have hH := P.radialH_smooth.comp harg (fun z _ =>
    div_nonneg (radiusSq_nonneg z.2) (sq_nonneg z.1))
  have hp : ContDiffOn ℝ ∞ (fun z : ℝ×PhysicalSpace => z.1^(-P.b)) {z | 0<z.1} := by
    apply contDiff_fst.contDiffOn.rpow_const_of_ne
    intro z hz
    exact ne_of_gt hz
  exact (hp.mul hH).congr (fun z _ => P.s0_radial z.2)

end SepticProfile

end
end

end OAI
