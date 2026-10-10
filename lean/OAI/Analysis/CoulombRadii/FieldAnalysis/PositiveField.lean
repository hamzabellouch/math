import Mathlib
import OAI.Analysis.CoulombRadii.FormDomain.BallTrial
import OAI.Analysis.CoulombRadii.Packets.ScaledWindow
import OAI.Analysis.CoulombRadii.FormDomain.FieldOptimization

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical SchwartzMap Pointwise
noncomputable section
namespace Coulomb

def ballTrialCoefficient : ℝ := ballKineticCoefficient+
  (1/2:ℝ)*(∑ b : Fin 3, ∫ x : Space, (fderiv ℝ unitWindow x (EuclideanSpace.single b 1))^2)+2

lemma ballTrialCoefficient_pos : 0 < ballTrialCoefficient := by
  unfold ballTrialCoefficient
  linarith [ballKineticCoefficient_pos,unitWindow_kinetic_nonneg]

theorem positive_field_ball_trial {J k : ℕ} (S : Nuclei J) (u : H1Vector k)
    (hu : Antisymmetric u) (hmu : mass u = 1)
    {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M)
    (y : Space) (A : Set Space) (hA : IsClosed A) (hsu : SpatiallySupported u A)
    (hcore : ∀ z ∈ A, 3*a ≤ ‖z-y‖) (hnuc : ∀ j, 3*a ≤ ‖S.position j-y‖) :
    unrestrictedFormBottom S ≤ ((form S u-M*coreScreenedField S u y+
      ballTrialCoefficient*(M^(5/3:ℝ)/a^2+M/a^2+M^2/a) : ℝ) : EReal) := by
  have H := ballCloud_trial S u hu hmu (scaledWindow unitWindow a ha.ne')
    (by rw [scaledWindow_mass unitWindow ha,unitWindow_mass])
    (scaledWindow_compactSupport unitWindow unitWindow_support ha)
    (scaledWindow_radial unitWindow unitWindow_radial ha)
    ha hM (scaledWindow_support unitWindow unitWindow_support ha)
    y A hA hsu hcore hnuc
  rw [scaledWindow_kinetic unitWindow ha] at H
  apply H.trans
  apply EReal.coe_le_coe_iff.mpr
  have hc : ballKineticCoefficient ≤ ballTrialCoefficient := by
    unfold ballTrialCoefficient
    linarith [unitWindow_kinetic_nonneg]
  have hg : (1/2:ℝ)*(∑ b : Fin 3, ∫ x : Space,
      (fderiv ℝ unitWindow x (EuclideanSpace.single b 1))^2) ≤ ballTrialCoefficient := by
    unfold ballTrialCoefficient
    linarith [ballKineticCoefficient_pos]
  have he : (5/4:ℝ) ≤ ballTrialCoefficient := by
    unfold ballTrialCoefficient
    linarith [ballKineticCoefficient_pos,unitWindow_kinetic_nonneg]
  have Hc := mul_le_mul_of_nonneg_right hc (show 0 ≤ M^(5/3:ℝ)/a^2 by positivity)
  have Hg := mul_le_mul_of_nonneg_right hg (show 0 ≤ M/a^2 by positivity)
  have He := mul_le_mul_of_nonneg_right he (show 0 ≤ M^2/a by positivity)
  linear_combination Hc+Hg+He

theorem positive_field_core_gain {J k : ℕ} (S : Nuclei J) (u : H1Vector k)
    (hu : Antisymmetric u) (hmu : mass u = 1)
    {a m : ℝ} (ha : 0 < a) (hm : 0 ≤ m)
    (ham : 1 ≤ a*m) (ham' : 1 ≤ a*m^(1/3:ℝ))
    (y : Space) (A : Set Space) (hA : IsClosed A) (hsu : SpatiallySupported u A)
    (hcore : ∀ z ∈ A, 3*a ≤ ‖z-y‖) (hnuc : ∀ j, 3*a ≤ ‖S.position j-y‖) :
    unrestrictedFormBottom S ≤ ((form S u-a*(max (coreScreenedField S u y) 0)^2/
      (16*ballTrialCoefficient)+4*ballTrialCoefficient*m^2/a : ℝ) : EReal) := by
  by_cases hb : unrestrictedFormBottom S = ⊥
  · simp [hb]
  have ht : unrestrictedFormBottom S ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _)
    (unrestrictedFormBottom_le_trial S u hu hmu)
  rw [←EReal.coe_toReal ht hb]
  apply EReal.coe_le_coe_iff.mpr
  apply positive_field_trial_optimization ha ballTrialCoefficient_pos hm ham ham'
  intro M hM
  apply EReal.coe_le_coe_iff.mp
  rw [EReal.coe_toReal ht hb]
  exact positive_field_ball_trial S u hu hmu ha hM y A hA hsu hcore hnuc

end Coulomb
end

end
end

end OAI
