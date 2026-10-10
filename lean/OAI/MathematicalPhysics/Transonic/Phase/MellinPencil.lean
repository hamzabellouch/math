import OAI.MathematicalPhysics.Transonic.Phase.SonicLinear

namespace OAI

section
noncomputable section
namespace SepticProfile
open Set Filter
open scoped ContDiff Topology BigOperators

lemma GlobalProfile.radialTT_smooth (P : GlobalProfile) : ContDiffOn ℝ ∞ P.radialTT (Ici 0) :=
  (P.radial_positive_powers_smooth ((1:ℝ)/3)).2.2.add
    ((contDiffOn_const.mul (P.radial_positive_powers_smooth (-(2:ℝ)/3)).2.2).mul (P.radialA_smooth.pow 2))
lemma GlobalProfile.radialCross_smooth (P : GlobalProfile) : ContDiffOn ℝ ∞ P.radialCross (Ici 0) :=
  ((contDiffOn_const.mul (P.radial_positive_powers_smooth (-(2:ℝ)/3)).2.2).mul P.radialA_smooth).mul P.radialC_smooth
lemma GlobalProfile.radialRR_smooth (P : GlobalProfile) : ContDiffOn ℝ ∞ P.radialRR (Ici 0) :=
  (P.radial_positive_powers_smooth ((1:ℝ)/3)).2.2.sub
    (((contDiffOn_const.mul contDiffOn_id).mul (P.radial_positive_powers_smooth (-(2:ℝ)/3)).2.2).mul (P.radialC_smooth.pow 2))
lemma GlobalProfile.mellinTimeFlux_smooth (P : GlobalProfile) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ici 0)) (a : ℝ) : ContDiffOn ℝ ∞ (P.mellinTimeFlux a f) (Ici 0) :=
  ((contDiffOn_const.mul P.radialTT_smooth).mul hf).sub
    (((contDiffOn_const.mul contDiffOn_id).mul (P.radialTT_smooth.sub P.radialCross_smooth)).mul
      (hf.derivWithin (uniqueDiffOn_Ici 0) (by simp)))
lemma GlobalProfile.mellinSpaceFlux_smooth (P : GlobalProfile) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ici 0)) (a : ℝ) : ContDiffOn ℝ ∞ (P.mellinSpaceFlux a f) (Ici 0) :=
  ((contDiffOn_const.mul P.radialCross_smooth).mul hf).add
    ((contDiffOn_const.mul (P.radialRR_smooth.add (contDiffOn_id.mul P.radialCross_smooth))).mul
      (hf.derivWithin (uniqueDiffOn_Ici 0) (by simp)))

def GlobalProfile.mellinPencil (P : GlobalProfile) (a : ℝ) (f : ℝ → ℝ) (z : ℝ) : ℝ :=
  (a-1-2*P.beta/3)*P.mellinTimeFlux a f z-
    2*z*derivWithin (P.mellinTimeFlux a f) (Ici 0) z-
    4*P.mellinSpaceFlux a f z-2*z*derivWithin (P.mellinSpaceFlux a f) (Ici 0) z

lemma GlobalProfile.linearized_time_flux_derivative (P : GlobalProfile) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ici 0)) (a : ℝ) {t : ℝ} (ht : 0<t) (X : PhysicalSpace) :
    partialTime (fun q Z => P.w0 q Z^2*partialTime (radialTrial a f) q Z+
      (2/3:ℝ)*P.w0 q Z^(-4:ℤ)*minkowskiPair P.s0 (radialTrial a f) q Z*partialTime P.s0 q Z) t X=
      t^((a-1-2*P.beta/3)-1)*((a-1-2*P.beta/3)*P.mellinTimeFlux a f (radiusSq X/t^2)-
        2*(radiusSq X/t^2)*derivWithin (P.mellinTimeFlux a f) (Ici 0) (radiusSq X/t^2)) := by
  have hd := radial_time_derivative (P.mellinTimeFlux_smooth hf a) (a-1-2*P.beta/3) ht X
  have he : (fun q => P.w0 q X^2*partialTime (radialTrial a f) q X+
      (2/3:ℝ)*P.w0 q X^(-4:ℤ)*minkowskiPair P.s0 (radialTrial a f) q X*partialTime P.s0 q X)=ᶠ[𝓝 t]
    (fun q => q^(a-1-2*P.beta/3)*P.mellinTimeFlux a f (radiusSq X/q^2)) := by
    filter_upwards [Ioi_mem_nhds ht] with q hq
    exact P.linearized_time_flux hf a hq X
  exact (hd.congr_of_eventuallyEq he).deriv

lemma GlobalProfile.linearized_space_flux_derivative (P : GlobalProfile) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ici 0)) (a : ℝ) {t : ℝ} (ht : 0<t)
    (X : PhysicalSpace) (j : Fin 4) :
    partialSpace (fun q Z => P.w0 q Z^2*partialSpace (radialTrial a f) j q Z+
      (2/3:ℝ)*P.w0 q Z^(-4:ℤ)*minkowskiPair P.s0 (radialTrial a f) q Z*partialSpace P.s0 j q Z) j t X=
      t^((a-1-2*P.beta/3)-1)*(P.mellinSpaceFlux a f (radiusSq X/t^2)+
        2*(X j)^2/t^2*derivWithin (P.mellinSpaceFlux a f) (Ici 0) (radiusSq X/t^2)) := by
  have hd := (radial_space_derivative (P.mellinSpaceFlux_smooth hf a) (t:=t) X j).const_mul
    (t^(a-1-2*P.beta/3)/t)
  have he : (fun r => P.w0 t (coordinateLine X j r)^2*partialSpace (radialTrial a f) j t (coordinateLine X j r)+
      (2/3:ℝ)*P.w0 t (coordinateLine X j r)^(-4:ℤ)*minkowskiPair P.s0 (radialTrial a f) t (coordinateLine X j r)*
      partialSpace P.s0 j t (coordinateLine X j r))=
    (fun r => (t^(a-1-2*P.beta/3)/t)*
      (P.mellinSpaceFlux a f (radiusSq (coordinateLine X j r)/t^2)*(coordinateLine X j r) j)) := by
    funext r
    rw [P.linearized_space_flux hf a ht]
    ring
  rw [partialSpace,he,hd.deriv,Real.rpow_sub_one (ne_of_gt ht)]

lemma GlobalProfile.linearized_radialTrial (P : GlobalProfile) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ici 0)) (a : ℝ) {t : ℝ} (ht : 0<t) (X : PhysicalSpace) :
    P.linearizedPhase (radialTrial a f) t X=t^(a-2-2*P.beta/3)*P.mellinPencil a f (radiusSq X/t^2) := by
  rw [GlobalProfile.linearizedPhase,P.linearized_time_flux_derivative hf a ht X]
  simp_rw [P.linearized_space_flux_derivative hf a ht X]
  rw [← Finset.mul_sum,sum_radial_divergence]
  have he : (a-1-2*P.beta/3)-1=a-2-2*P.beta/3 := by ring
  rw [he]
  unfold GlobalProfile.mellinPencil
  ring

end SepticProfile

end
end

end OAI
