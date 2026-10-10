import OAI.MathematicalPhysics.Transonic.Phase.MellinWeights

namespace OAI

section
noncomputable section
namespace SepticProfile
open Set
open scoped ContDiff BigOperators

def GlobalProfile.radialTT (P : GlobalProfile) (z : ℝ) : ℝ :=
  P.radialM z^((1:ℝ)/3)+(2/3:ℝ)*P.radialM z^(-(2:ℝ)/3)*P.radialA z^2
def GlobalProfile.radialCross (P : GlobalProfile) (z : ℝ) : ℝ :=
  (2/3:ℝ)*P.radialM z^(-(2:ℝ)/3)*P.radialA z*P.radialC z
def GlobalProfile.radialRR (P : GlobalProfile) (z : ℝ) : ℝ :=
  P.radialM z^((1:ℝ)/3)-(2/3:ℝ)*z*P.radialM z^(-(2:ℝ)/3)*P.radialC z^2

def GlobalProfile.mellinTimeFlux (P : GlobalProfile) (a : ℝ) (f : ℝ → ℝ) (z : ℝ) : ℝ :=
  a*P.radialTT z*f z-2*z*(P.radialTT z-P.radialCross z)*derivWithin f (Ici 0) z
def GlobalProfile.mellinSpaceFlux (P : GlobalProfile) (a : ℝ) (f : ℝ → ℝ) (z : ℝ) : ℝ :=
  -a*P.radialCross z*f z+2*(P.radialRR z+z*P.radialCross z)*derivWithin f (Ici 0) z

lemma GlobalProfile.s0_partialTime_radial (P : GlobalProfile) {t : ℝ} (ht : 0<t)
    (X : PhysicalSpace) :
    partialTime P.s0 t X= -t^(-P.beta)*P.radialA (radiusSq X/t^2) := by
  rw [partialTime,(P.s0_time_derivative ht X).deriv,← P.radialA_sq,div_pow,radius_sq]

lemma GlobalProfile.s0_partialSpace_radial (P : GlobalProfile) {t : ℝ} (ht : 0<t)
    (X : PhysicalSpace) (j : Fin 4) :
    partialSpace P.s0 j t X=t^(-P.beta)*P.radialC (radiusSq X/t^2)*(X j/t) := by
  rw [partialSpace,(P.s0_coordinate_derivative_simple ht X j).deriv]
  have he : P.A (radius X/t)*P.g (radiusSq X/t^2)=P.radialC (radiusSq X/t^2) := by
    have hy : (radius X/t)^2=radiusSq X/t^2 := by rw [div_pow,radius_sq]
    rw [← hy,P.radialC_sq]
  calc
    _=t^(-P.beta)*(P.A (radius X/t)*P.g (radiusSq X/t^2))*(X j/t) := by ring
    _=_ := by rw [he]

lemma GlobalProfile.pair_radialTrial (P : GlobalProfile) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ici 0)) (a : ℝ) {t : ℝ} (ht : 0<t) (X : PhysicalSpace) :
    minkowskiPair P.s0 (radialTrial a f) t X=
      t^(-P.beta)*t^(a-1)*(-a*P.radialA (radiusSq X/t^2)*f (radiusSq X/t^2)+
        2*(radiusSq X/t^2)*(P.radialA (radiusSq X/t^2)-P.radialC (radiusSq X/t^2))*
          derivWithin f (Ici 0) (radiusSq X/t^2)) := by
  rw [minkowskiPair,P.s0_partialTime_radial ht X,radialTrial_time hf a ht X]
  simp_rw [P.s0_partialSpace_radial ht X,radialTrial_space hf a ht X]
  have he (j : Fin 4) :
      t^(-P.beta)*P.radialC (radiusSq X/t^2)*(X j/t)*
        (t^(a-1)*2*(X j/t)*derivWithin f (Ici 0) (radiusSq X/t^2))=
      (2*t^(-P.beta)*t^(a-1)*P.radialC (radiusSq X/t^2)*
        derivWithin f (Ici 0) (radiusSq X/t^2)/t^2)*X j^2 := by ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  change _-(2*t^(-P.beta)*t^(a-1)*P.radialC (radiusSq X/t^2)*
    derivWithin f (Ici 0) (radiusSq X/t^2)/t^2)*radiusSq X=_
  ring

lemma GlobalProfile.linearized_time_flux (P : GlobalProfile) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ici 0)) (a : ℝ) {t : ℝ} (ht : 0<t) (X : PhysicalSpace) :
    P.w0 t X^2*partialTime (radialTrial a f) t X+
      (2/3:ℝ)*P.w0 t X^(-4:ℤ)*minkowskiPair P.s0 (radialTrial a f) t X*partialTime P.s0 t X=
    t^(a-1-2*P.beta/3)*P.mellinTimeFlux a f (radiusSq X/t^2) := by
  rw [radialTrial_time hf a ht X,P.pair_radialTrial hf a ht X,P.s0_partialTime_radial ht X]
  let z := radiusSq X/t^2
  change P.w0 t X^2*(t^(a-1)*(a*f z-2*z*derivWithin f (Ici 0) z))+
    (2/3:ℝ)*P.w0 t X^(-4:ℤ)*(t^(-P.beta)*t^(a-1)*(-a*P.radialA z*f z+
      2*z*(P.radialA z-P.radialC z)*derivWithin f (Ici 0) z))*(-t^(-P.beta)*P.radialA z)=_
  calc
    _=P.w0 t X^2*t^(a-1)*(a*f z-2*z*derivWithin f (Ici 0) z)+
      (2/3:ℝ)*(P.w0 t X^(-4:ℤ)*(t^(-P.beta))^2)*t^(a-1)*P.radialA z*
        (a*P.radialA z*f z-2*z*(P.radialA z-P.radialC z)*derivWithin f (Ici 0) z) := by ring
    _=(t^(-2*P.beta/3)*t^(a-1))*P.mellinTimeFlux a f z := by
      rw [P.w0_square ht X,P.w0_inverse_fourth_scaled ht X]
      dsimp only [GlobalProfile.mellinTimeFlux,GlobalProfile.radialTT,GlobalProfile.radialCross,z]
      ring
    _=_ := by
      rw [← Real.rpow_add ht]
      congr 2
      ring

lemma GlobalProfile.linearized_space_flux (P : GlobalProfile) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ici 0)) (a : ℝ) {t : ℝ} (ht : 0<t)
    (X : PhysicalSpace) (j : Fin 4) :
    P.w0 t X^2*partialSpace (radialTrial a f) j t X+
      (2/3:ℝ)*P.w0 t X^(-4:ℤ)*minkowskiPair P.s0 (radialTrial a f) t X*partialSpace P.s0 j t X=
    t^(a-1-2*P.beta/3)/t*P.mellinSpaceFlux a f (radiusSq X/t^2)*X j := by
  rw [radialTrial_space hf a ht X,P.pair_radialTrial hf a ht X,P.s0_partialSpace_radial ht X j]
  let z := radiusSq X/t^2
  change P.w0 t X^2*(t^(a-1)*2*(X j/t)*derivWithin f (Ici 0) z)+
    (2/3:ℝ)*P.w0 t X^(-4:ℤ)*(t^(-P.beta)*t^(a-1)*(-a*P.radialA z*f z+
      2*z*(P.radialA z-P.radialC z)*derivWithin f (Ici 0) z))*(t^(-P.beta)*P.radialC z*(X j/t))=_
  calc
    _=(P.w0 t X^2*t^(a-1)*2*derivWithin f (Ici 0) z+
      (2/3:ℝ)*(P.w0 t X^(-4:ℤ)*(t^(-P.beta))^2)*t^(a-1)*P.radialC z*
        (-a*P.radialA z*f z+2*z*(P.radialA z-P.radialC z)*derivWithin f (Ici 0) z))*(X j/t) := by ring
    _=(t^(-2*P.beta/3)*t^(a-1))*P.mellinSpaceFlux a f z*(X j/t) := by
      rw [P.w0_square ht X,P.w0_inverse_fourth_scaled ht X]
      dsimp only [GlobalProfile.mellinSpaceFlux,GlobalProfile.radialRR,GlobalProfile.radialCross,z]
      ring
    _=_ := by
      have he : t^(-2*P.beta/3)*t^(a-1)=t^(a-1-2*P.beta/3) := by
        rw [← Real.rpow_add ht]
        congr 1
        ring
      rw [he]
      ring

end SepticProfile

end
end

end OAI
