import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFinitePoleInverse

namespace OAI

/-! The local meromorphic formula agrees with the actual inverse on a
punctured neighborhood of each positive real parameter below two. -/
noncomputable section
open Filter Topology
namespace CubicFirstMoment

lemma cubicThetaLocalEnergyResolvent_eq_inverse {z : ℝ} (hz : z≠0) {w : ℂ}
    (hw : w≠(z:ℂ))
    (hu : IsUnit (cubicThetaEnergyPencil w+cubicThetaExceptionalProjection (z:ℂ))) :
    cubicThetaLocalEnergyResolvent (z:ℂ) w=Ring.inverse (cubicThetaEnergyPencil w) := by
  have hcz : (z:ℂ)≠0 := by exact_mod_cast hz
  have hTP := cubicThetaEnergyPencil_mul_projection hz w
  have hPT : cubicThetaExceptionalProjection (z:ℂ)*cubicThetaEnergyPencil w=
      (1-w/(z:ℂ)) • cubicThetaExceptionalProjection (z:ℂ) := by
    exact (cubicThetaEnergyPencil_commute_projection hz w).eq.symm.trans hTP
  have hc : 1-w/(z:ℂ)≠0 := by
    apply sub_ne_zero.mpr
    intro he
    exact hw ((div_eq_one_iff_eq hcz).mp he.symm)
  have hcoef : (1-w/(z:ℂ))⁻¹=(z:ℂ)/((z:ℂ)-w) := by
    have he : 1-w/(z:ℂ)=((z:ℂ)-w)/(z:ℂ) := by field_simp
    rw [he,inv_div]
  rw [cubicThetaLocalEnergyResolvent,← hcoef]
  exact (cubicThetaProjection_inverse _ _ _
    (cubicThetaExceptionalProjection_idempotent _) hTP hPT hu hc).symm

lemma cubicThetaEnergyPencil_unit_near_real {z : ℝ} (hz : 0<z) (hz2 : z<2) :
    ∀ᶠ w : ℂ in 𝓝[≠] (z:ℂ), IsUnit (cubicThetaEnergyPencil w) := by
  have hu := cubicThetaProjectedPencil_unit hz.le hz2
  have ha := (cubicThetaEnergyPencil_analytic (z:ℂ)).add
    (show AnalyticAt ℂ (fun _ : ℂ => cubicThetaExceptionalProjection (z:ℂ)) (z:ℂ)
      from analyticAt_const)
  have hunit : ∀ᶠ w : ℂ in 𝓝 (z:ℂ),
      IsUnit (cubicThetaEnergyPencil w+cubicThetaExceptionalProjection (z:ℂ)) :=
    by
      have hn : {A : cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace | IsUnit A} ∈
          𝓝 (cubicThetaEnergyPencil (z:ℂ)+cubicThetaExceptionalProjection (z:ℂ)) :=
        (Units.isOpen (R:=cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace)).mem_nhds hu
      exact ha.continuousAt.eventually hn
  filter_upwards [nhdsWithin_le_nhds hunit,self_mem_nhdsWithin] with w hwu hw
  have hcz : (z:ℂ)≠0 := by exact_mod_cast hz.ne'
  have hc : 1-w/(z:ℂ)≠0 := by
    apply sub_ne_zero.mpr
    intro he
    exact hw ((div_eq_one_iff_eq hcz).mp he.symm)
  have hTP := cubicThetaEnergyPencil_mul_projection hz.ne' w
  exact (cubicThetaProjection_inverse_data _ _ _
    (cubicThetaExceptionalProjection_idempotent _) hTP
    ((cubicThetaEnergyPencil_commute_projection hz.ne' w).eq.symm.trans hTP) hwu hc).1

theorem cubicThetaEnergyInverse_meromorphic_real {z : ℝ} (hz : 0<z) (hz2 : z<2) :
    MeromorphicAt (fun w : ℂ => Ring.inverse (cubicThetaEnergyPencil w)) (z:ℂ) := by
  have hu := cubicThetaProjectedPencil_unit hz.le hz2
  have ha := (cubicThetaEnergyPencil_analytic (z:ℂ)).add
    (show AnalyticAt ℂ (fun _ : ℂ => cubicThetaExceptionalProjection (z:ℂ)) (z:ℂ)
      from analyticAt_const)
  have hunit : ∀ᶠ w : ℂ in 𝓝 (z:ℂ),
      IsUnit (cubicThetaEnergyPencil w+cubicThetaExceptionalProjection (z:ℂ)) :=
    by
      have hn : {A : cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace | IsUnit A} ∈
          𝓝 (cubicThetaEnergyPencil (z:ℂ)+cubicThetaExceptionalProjection (z:ℂ)) :=
        (Units.isOpen (R:=cubicThetaGlobalEnergySpace →L[ℂ] cubicThetaGlobalEnergySpace)).mem_nhds hu
      exact ha.continuousAt.eventually hn
  apply (cubicThetaLocalEnergyResolvent_meromorphic hz.le hz2).congr
  filter_upwards [nhdsWithin_le_nhds hunit,self_mem_nhdsWithin] with w hwu hw
  exact cubicThetaLocalEnergyResolvent_eq_inverse hz.ne' (by simpa using hw) hwu

end CubicFirstMoment

end

end OAI
