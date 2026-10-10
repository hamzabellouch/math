import OAI.MathematicalPhysics.Transonic.Phase.MellinPencil

namespace OAI

section
noncomputable section
namespace SepticProfile
open Set
open scoped ContDiff

def GlobalProfile.mellinTZero (P : GlobalProfile) (a z : ℝ) : ℝ := a*P.radialTT z
def GlobalProfile.mellinTFirst (P : GlobalProfile) (z : ℝ) : ℝ := -2*z*(P.radialTT z-P.radialCross z)
def GlobalProfile.mellinSZero (P : GlobalProfile) (a z : ℝ) : ℝ := -a*P.radialCross z
def GlobalProfile.mellinSFirst (P : GlobalProfile) (z : ℝ) : ℝ := 2*(P.radialRR z+z*P.radialCross z)

def GlobalProfile.mellinSecondCoeff (P : GlobalProfile) (z : ℝ) : ℝ :=
  -2*z*(P.mellinTFirst z+P.mellinSFirst z)
def GlobalProfile.mellinFirstCoeff (P : GlobalProfile) (a z : ℝ) : ℝ :=
  (a-1-2*P.beta/3)*P.mellinTFirst z-
    2*z*(P.mellinTZero a z+derivWithin P.mellinTFirst (Ici 0) z)-
    4*P.mellinSFirst z-2*z*(P.mellinSZero a z+derivWithin P.mellinSFirst (Ici 0) z)
def GlobalProfile.mellinZeroCoeff (P : GlobalProfile) (a z : ℝ) : ℝ :=
  (a-1-2*P.beta/3)*P.mellinTZero a z-
    2*z*derivWithin (P.mellinTZero a) (Ici 0) z-
    4*P.mellinSZero a z-2*z*derivWithin (P.mellinSZero a) (Ici 0) z

lemma GlobalProfile.mellinTZero_smooth (P : GlobalProfile) (a : ℝ) :
    ContDiffOn ℝ ∞ (P.mellinTZero a) (Ici 0) := contDiffOn_const.mul P.radialTT_smooth
lemma GlobalProfile.mellinTFirst_smooth (P : GlobalProfile) :
    ContDiffOn ℝ ∞ P.mellinTFirst (Ici 0) :=
  (contDiffOn_const.mul contDiffOn_id).mul (P.radialTT_smooth.sub P.radialCross_smooth)
lemma GlobalProfile.mellinSZero_smooth (P : GlobalProfile) (a : ℝ) :
    ContDiffOn ℝ ∞ (P.mellinSZero a) (Ici 0) := contDiffOn_const.mul P.radialCross_smooth
lemma GlobalProfile.mellinSFirst_smooth (P : GlobalProfile) :
    ContDiffOn ℝ ∞ P.mellinSFirst (Ici 0) :=
  contDiffOn_const.mul (P.radialRR_smooth.add (contDiffOn_id.mul P.radialCross_smooth))
lemma GlobalProfile.mellinSecondCoeff_smooth (P : GlobalProfile) :
    ContDiffOn ℝ ∞ P.mellinSecondCoeff (Ici 0) :=
  (contDiffOn_const.mul contDiffOn_id).mul (P.mellinTFirst_smooth.add P.mellinSFirst_smooth)

lemma smooth_flux_pair_derivative {C D f : ℝ → ℝ}
    (hC : ContDiffOn ℝ ∞ C (Ici 0)) (hD : ContDiffOn ℝ ∞ D (Ici 0))
    (hf : ContDiffOn ℝ ∞ f (Ici 0)) {z : ℝ} (hz : 0≤z) :
    derivWithin (fun q => C q*f q+D q*derivWithin f (Ici 0) q) (Ici 0) z=
      derivWithin C (Ici 0) z*f z+
      (C z+derivWithin D (Ici 0) z)*derivWithin f (Ici 0) z+
      D z*derivWithin (derivWithin f (Ici 0)) (Ici 0) z := by
  have hc := (hC.differentiableOn (by simp) z hz).hasDerivWithinAt
  have hd := (hD.differentiableOn (by simp) z hz).hasDerivWithinAt
  have h := (hf.differentiableOn (by simp) z hz).hasDerivWithinAt
  have hfs : ContDiffOn ℝ ∞ (derivWithin f (Ici 0)) (Ici 0) :=
    hf.derivWithin (uniqueDiffOn_Ici 0) (by simp)
  have h' := (hfs.differentiableOn (by simp) z hz).hasDerivWithinAt
  change derivWithin (C*f+D*derivWithin f (Ici 0)) (Ici 0) z=_
  rw [((hc.mul h).add (hd.mul h')).derivWithin (uniqueDiffOn_Ici 0 z hz)]
  ring

lemma GlobalProfile.mellinPencil_coefficients (P : GlobalProfile) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ici 0)) (a : ℝ) {z : ℝ} (hz : 0≤z) :
    P.mellinPencil a f z=P.mellinSecondCoeff z*derivWithin (derivWithin f (Ici 0)) (Ici 0) z+
      P.mellinFirstCoeff a z*derivWithin f (Ici 0) z+P.mellinZeroCoeff a z*f z := by
  have ht : P.mellinTimeFlux a f=(fun q => P.mellinTZero a q*f q+
      P.mellinTFirst q*derivWithin f (Ici 0) q) := by
    funext q
    dsimp only [GlobalProfile.mellinTimeFlux,GlobalProfile.mellinTZero,GlobalProfile.mellinTFirst]
    ring
  have hs : P.mellinSpaceFlux a f=(fun q => P.mellinSZero a q*f q+
      P.mellinSFirst q*derivWithin f (Ici 0) q) := by
    funext q
    rfl
  rw [GlobalProfile.mellinPencil,ht,hs,
    smooth_flux_pair_derivative (P.mellinTZero_smooth a) P.mellinTFirst_smooth hf hz,
    smooth_flux_pair_derivative (P.mellinSZero_smooth a) P.mellinSFirst_smooth hf hz]
  dsimp only [GlobalProfile.mellinSecondCoeff,GlobalProfile.mellinFirstCoeff,GlobalProfile.mellinZeroCoeff]
  ring

lemma GlobalProfile.mellinSecondCoeff_factor (P : GlobalProfile) (z : ℝ) :
    P.mellinSecondCoeff z=4*z*(z*P.radialTT z-2*z*P.radialCross z-P.radialRR z) := by
  dsimp only [GlobalProfile.mellinSecondCoeff,GlobalProfile.mellinTFirst,GlobalProfile.mellinSFirst]
  ring

lemma GlobalProfile.mellinSecondCoeff_sq (P : GlobalProfile) (y : ℝ) :
    P.mellinSecondCoeff (y^2)=4*y^2*P.mellinPrincipal y := by
  rw [P.mellinSecondCoeff_factor]
  dsimp only [GlobalProfile.radialTT,GlobalProfile.radialCross,GlobalProfile.radialRR,
    GlobalProfile.mellinPrincipal,GlobalProfile.timeTensor,GlobalProfile.mixedTensor,GlobalProfile.radialTensor]
  rw [P.radialM_sq,P.radialA_sq,P.B_radial]
  ring

lemma GlobalProfile.mellinSecondCoeff_axis (P : GlobalProfile) : P.mellinSecondCoeff 0=0 := by
  rw [P.mellinSecondCoeff_factor]
  ring
lemma GlobalProfile.mellinSecondCoeff_sonic (P : GlobalProfile) :
    P.mellinSecondCoeff ((sonicRadius P.beta)^2)=0 := by
  rw [P.mellinSecondCoeff_sq,P.mellinPrincipal_sonic,mul_zero]

lemma GlobalProfile.mellinPencil_sonic (P : GlobalProfile) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ici 0)) (a : ℝ) :
    P.mellinPencil a f ((sonicRadius P.beta)^2)=
      P.mellinFirstCoeff a ((sonicRadius P.beta)^2)*derivWithin f (Ici 0) ((sonicRadius P.beta)^2)+
      P.mellinZeroCoeff a ((sonicRadius P.beta)^2)*f ((sonicRadius P.beta)^2) := by
  rw [P.mellinPencil_coefficients hf a (sq_nonneg _),P.mellinSecondCoeff_sonic,zero_mul,zero_add]

end SepticProfile

end
end

end OAI
