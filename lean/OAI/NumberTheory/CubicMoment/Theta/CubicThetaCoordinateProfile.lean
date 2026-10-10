import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoordinateNormBounds
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGeometricNumerics

namespace OAI

/-! Pointwise geometric majorants beyond the finite coordinate boxes. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

def cubicThetaRadiusProfile (κ r : ℝ) : ℝ := r^2*Real.exp (-κ*r)

lemma cubicThetaRadiusProfile_derivative (κ r : ℝ) :
    HasDerivAt (cubicThetaRadiusProfile κ) (r*(2-κ*r)*Real.exp (-κ*r)) r := by
  have hp : HasDerivAt (fun t : ℝ => t^2) (2*r) r := by
    convert (hasDerivAt_id r).pow 2 using 1
    · funext t; rfl
    · norm_num [id_eq]
  have he : HasDerivAt (fun t : ℝ => -κ*t) (-κ) r := by
    convert (hasDerivAt_id r).const_mul (-κ) using 1
    · funext t; rfl
    · simp
  convert hp.mul he.exp using 1
  · rfl
  · ring

lemma cubicThetaRadiusProfile_antitone {κ : ℝ} (hκ : 2≤κ) :
    AntitoneOn (cubicThetaRadiusProfile κ) (Ici 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici _) (by unfold cubicThetaRadiusProfile; fun_prop)
    (fun r _ => (cubicThetaRadiusProfile_derivative κ r).differentiableAt.differentiableWithinAt)
  intro r hr
  rw [(cubicThetaRadiusProfile_derivative κ r).deriv]
  have hr' : 1≤r := interior_subset hr
  have hκr : 2≤κ*r := by nlinarith
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)) (Real.exp_pos _).le

def cubicThetaPrimaryTailMass (p : CubicThetaIntegerPoint) : ℝ :=
  cubicThetaPrimaryQuadratic p*Real.exp (-(241/100:ℝ)*Real.sqrt (cubicThetaPrimaryQuadratic p))

def cubicThetaRamifiedTailMass (p : CubicThetaIntegerPoint) : ℝ :=
  cubicThetaIntegerQuadratic p*Real.exp (-(29/4:ℝ)*Real.sqrt (cubicThetaIntegerQuadratic p))

lemma cubicThetaPrimaryTailMass_bound (p : CubicThetaIntegerPoint)
    (hp : 2≤cubicThetaIntegerRadius p) :
    cubicThetaPrimaryTailMass p≤4*(cubicThetaIntegerRadius p:ℝ)^2*
      Real.exp (-(241/50:ℝ)*(cubicThetaIntegerRadius p:ℝ)) := by
  have hk : (2:ℝ)≤cubicThetaIntegerRadius p := by exact_mod_cast hp
  have hN : 0≤cubicThetaPrimaryQuadratic p :=
    cubicThetaQuadratic_nonneg (1+3*(p.1:ℝ)) (3*(p.2:ℝ))
  have hr := cubicThetaPrimaryQuadratic_sqrt_lower p hp
  have h := cubicThetaRadiusProfile_antitone (by norm_num : (2:ℝ)≤241/100)
    (by change 1≤2*(cubicThetaIntegerRadius p:ℝ); linarith)
    (by change 1≤Real.sqrt (cubicThetaPrimaryQuadratic p); linarith) hr
  unfold cubicThetaRadiusProfile at h
  rw [Real.sq_sqrt hN] at h
  unfold cubicThetaPrimaryTailMass
  convert h using 1
  ring_nf

lemma cubicThetaRamifiedTailMass_bound (p : CubicThetaIntegerPoint)
    (hp : 2≤cubicThetaIntegerRadius p) :
    cubicThetaRamifiedTailMass p≤(cubicThetaIntegerRadius p:ℝ)^2*
      Real.exp (-(6:ℝ)*(cubicThetaIntegerRadius p:ℝ)) := by
  have hk : (2:ℝ)≤cubicThetaIntegerRadius p := by exact_mod_cast hp
  have hN : 0≤cubicThetaIntegerQuadratic p := cubicThetaQuadratic_nonneg (p.1:ℝ) p.2
  have hr := cubicThetaIntegerQuadratic_sqrt_lower p
  have h := cubicThetaRadiusProfile_antitone (by norm_num : (2:ℝ)≤29/4)
    (by change 1≤(6/7:ℝ)*(cubicThetaIntegerRadius p:ℝ); linarith)
    (by change 1≤Real.sqrt (cubicThetaIntegerQuadratic p); linarith) hr
  unfold cubicThetaRadiusProfile at h
  rw [Real.sq_sqrt hN] at h
  unfold cubicThetaRamifiedTailMass
  apply h.trans
  apply mul_le_mul
  · nlinarith [sq_nonneg (cubicThetaIntegerRadius p:ℝ)]
  · apply Real.exp_le_exp.mpr
    nlinarith
  · exact (Real.exp_pos _).le
  · positivity

end CubicFirstMoment

end

end OAI
