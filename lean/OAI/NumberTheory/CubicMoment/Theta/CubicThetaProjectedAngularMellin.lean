import OAI.NumberTheory.CubicMoment.Theta.CubicThetaProjectedAngular
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaBoundedScaledMellin
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaLevelAngularReciprocity
import OAI.NumberTheory.CubicMoment.Estimates.ThetaMellinAngularFunctional

namespace OAI

/-! Entire Mellin continuation for the two actual coefficient families
in the primary-projected rational-cusp transformation. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaProjectedAngularAxis (g : SL(2,Eisenstein)) (hc : primary (g 1 0))
    (rev : Bool) (k : ℕ) : ℝ→ℂ :=
  cubicThetaBoundedScaledAxis (cubicThetaProjectedCoefficient g hc) (cubicThetaCircleOrder rev k)
    (cubicThetaPrimaryDualCenter g) (cubicThetaLevelScale (g 1 0))

def cubicThetaSelectedAngularAxis (g : SL(2,Eisenstein)) (rev : Bool) (k : ℕ) : ℝ→ℂ :=
  cubicThetaBoundedScaledAxis cubicThetaSelectedCoefficient (cubicThetaCircleOrder (!rev) k)
    (cubicThetaPrimaryCuspCenter g) (cubicThetaLevelScale (g 1 0))

lemma cubicThetaSelectedCoefficient_arithmetic_bound (n : Eisenstein) (hn : n≠0) :
    ‖cubicThetaSelectedCoefficient n‖≤81*norm n :=
  (cubicThetaSelectedCoefficient_norm n).trans
    (le_mul_of_one_le_right (by norm_num) (one_le_norm hn))

theorem cubicThetaProjectedAngularAxis_functional (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) {k : ℕ} (hk : 0<k)
    {t : ℝ} (ht : 0<t) :
    cubicThetaProjectedAngularAxis g hc rev k (1/t)=
      cubicThetaLevelAngularRoot (g 1 0) rev k*(t:ℂ)^(2*k)*
        cubicThetaSelectedAngularAxis g rev k t := by
  have hv := mul_pos (cubicThetaLevelScale_pos hc) (inv_pos.mpr ht)
  have H := cubicThetaSelected_projected_angular g hc hv rev hk
  rw [cubicThetaLevelScale_reciprocal hc (inv_pos.mpr ht),inv_inv,
    cubicThetaLevelAngular_scaled_direction hc ht,cubicThetaCircleMultiplier_real_mul] at H
  simpa only [cubicThetaProjectedAngularAxis,cubicThetaSelectedAngularAxis,
    cubicThetaBoundedScaledAxis,cubicThetaLevelAngularRoot,one_div,mul_pow,pow_mul,mul_assoc] using H

def cubicThetaProjectedAngularCompleted (g : SL(2,Eisenstein)) (hc : primary (g 1 0))
    (rev : Bool) (k : ℕ) (s : ℂ) : ℂ :=
  mellin (thetaUpper (cubicThetaProjectedAngularAxis g hc rev k)) s+
    cubicThetaLevelAngularRoot (g 1 0) rev k*
      mellin (thetaUpper (cubicThetaSelectedAngularAxis g rev k)) (((2*k:ℕ):ℂ)-s)

theorem cubicThetaProjectedAngular_mellin (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) {k : ℕ} (hk : 0<k) (s : ℂ) :
    MellinConvergent (cubicThetaProjectedAngularAxis g hc rev k) s ∧
      mellin (cubicThetaProjectedAngularAxis g hc rev k) s=
        cubicThetaProjectedAngularCompleted g hc rev k s := by
  apply theta_mellin_split_angular k
    (fun t ht => cubicThetaProjectedAngularAxis_functional g hc rev hk ht)
  · exact cubicThetaBoundedScaledUpper_mellinConvergent (by norm_num : (0:ℝ)≤243)
      (cubicThetaProjectedCoefficient_arithmetic_bound g hc) _ _ (cubicThetaLevelScale_pos hc) s
  · exact cubicThetaBoundedScaledUpper_mellinConvergent (by norm_num : (0:ℝ)≤81)
      cubicThetaSelectedCoefficient_arithmetic_bound _ _ (cubicThetaLevelScale_pos hc) _

theorem cubicThetaProjectedAngularCompleted_entire (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) (k : ℕ) :
    Differentiable ℂ (cubicThetaProjectedAngularCompleted g hc rev k) := by
  have hf := cubicThetaBoundedScaledUpper_entire (by norm_num : (0:ℝ)≤243)
    (cubicThetaProjectedCoefficient_arithmetic_bound g hc) (cubicThetaCircleOrder rev k)
    (cubicThetaPrimaryDualCenter g) (cubicThetaLevelScale_pos hc)
  have hg := cubicThetaBoundedScaledUpper_entire (by norm_num : (0:ℝ)≤81)
    cubicThetaSelectedCoefficient_arithmetic_bound (cubicThetaCircleOrder (!rev) k)
    (cubicThetaPrimaryCuspCenter g) (cubicThetaLevelScale_pos hc)
  have hlin : Differentiable ℂ (fun s : ℂ => ((2*k:ℕ):ℂ)-s) := by fun_prop
  exact hf.add ((hg.comp hlin).const_mul _)

theorem cubicThetaProjectedAngularCompleted_functional (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) {k : ℕ} (hk : 0<k) (s : ℂ) :
    cubicThetaProjectedAngularCompleted g hc rev k s=
      cubicThetaLevelAngularRoot (g 1 0) rev k*
        mellin (cubicThetaSelectedAngularAxis g rev k) (((2*k:ℕ):ℂ)-s) := by
  rw [←(cubicThetaProjectedAngular_mellin g hc rev hk s).2]
  exact theta_mellin_functional_angular k
    (fun t ht => cubicThetaProjectedAngularAxis_functional g hc rev hk ht) s

theorem cubicThetaProjectedAngular_actual_entire (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) {k : ℕ} (hk : 0<k) :
    Differentiable ℂ (mellin (cubicThetaProjectedAngularAxis g hc rev k)) := by
  have he : mellin (cubicThetaProjectedAngularAxis g hc rev k)=
      cubicThetaProjectedAngularCompleted g hc rev k := by
    funext s
    exact (cubicThetaProjectedAngular_mellin g hc rev hk s).2
  rw [he]
  exact cubicThetaProjectedAngularCompleted_entire g hc rev k

end CubicFirstMoment

end

end OAI
