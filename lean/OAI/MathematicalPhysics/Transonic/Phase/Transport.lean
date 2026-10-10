import OAI.MathematicalPhysics.Transonic.Phase.MellinFlux

namespace OAI

section
noncomputable section
namespace SepticProfile
open Set Filter
open scoped ContDiff Topology BigOperators

lemma GlobalProfile.time_flux_derivative (P : GlobalProfile) {t : ℝ} (ht : 0<t)
    (X : PhysicalSpace) :
    partialTime (fun q Z => (minkowskiSquare P.s0 q Z)^((1:ℝ)/3)*partialTime P.s0 q Z) t X=
      t^(-ell*P.beta-1)*(ell*P.beta*P.radialF (radiusSq X/t^2)+
        2*(radiusSq X/t^2)*derivWithin P.radialF (Ici 0) (radiusSq X/t^2)) := by
  have hd := (radial_time_derivative P.radialF_smooth (-ell*P.beta) ht X).neg
  have he : (fun q => (minkowskiSquare P.s0 q X)^((1:ℝ)/3)*partialTime P.s0 q X)=ᶠ[𝓝 t]
      (fun q => -(q^(-ell*P.beta)*P.radialF (radiusSq X/q^2))) := by
    filter_upwards [Ioi_mem_nhds ht] with q hq
    simpa only [neg_mul] using P.time_flux hq X
  have hc := hd.congr_of_eventuallyEq he
  rw [partialTime,hc.deriv]
  ring

lemma GlobalProfile.space_flux_derivative (P : GlobalProfile) {t : ℝ} (ht : 0<t)
    (X : PhysicalSpace) (j : Fin 4) :
    partialSpace (fun q Z => (minkowskiSquare P.s0 q Z)^((1:ℝ)/3)*partialSpace P.s0 j q Z) j t X=
      t^(-ell*P.beta-1)*(P.radialJ (radiusSq X/t^2)+
        2*(X j)^2/t^2*derivWithin P.radialJ (Ici 0) (radiusSq X/t^2)) := by
  have hd := (radial_space_derivative P.radialJ_smooth (t:=t) X j).const_mul (t^(-ell*P.beta)/t)
  have he : (fun r => (minkowskiSquare P.s0 t (coordinateLine X j r))^((1:ℝ)/3)*
      partialSpace P.s0 j t (coordinateLine X j r))=
      (fun r => (t^(-ell*P.beta)/t)*
        (P.radialJ (radiusSq (coordinateLine X j r)/t^2)*(coordinateLine X j r) j)) := by
    funext r
    rw [P.space_flux ht]
    ring
  rw [partialSpace,he,hd.deriv,Real.rpow_sub_one (ne_of_gt ht)]

lemma sum_radial_divergence (X : PhysicalSpace) (t a b : ℝ) :
    (∑ j : Fin 4, (a+2*(X j)^2/t^2*b))=4*a+2*(radiusSq X/t^2)*b := by
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_ofNat]
  have he (j : Fin 4) : 2*X j^2/t^2*b=(2*b/t^2)*X j^2 := by ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  change 4*a+(2*b/t^2)*radiusSq X=4*a+2*(radiusSq X/t^2)*b
  ring

lemma GlobalProfile.s0_transport (P : GlobalProfile) {t : ℝ} (ht : 0<t)
    (X : PhysicalSpace) : phaseTransport P.s0 t X=0 := by
  rw [phaseTransport,P.time_flux_derivative ht X]
  simp_rw [P.space_flux_derivative ht X]
  rw [← Finset.mul_sum,sum_radial_divergence]
  calc
    _=t^(-ell*P.beta-1)*(ell*P.beta*P.radialF (radiusSq X/t^2)+
      2*(radiusSq X/t^2)*derivWithin P.radialF (Ici 0) (radiusSq X/t^2)-
      4*P.radialJ (radiusSq X/t^2)-
      2*(radiusSq X/t^2)*derivWithin P.radialJ (Ici 0) (radiusSq X/t^2)) := by ring
    _=0 := by rw [P.radial_transport_sq (div_nonneg (radiusSq_nonneg X) (sq_nonneg t)),mul_zero]

end SepticProfile

end
end

end OAI
