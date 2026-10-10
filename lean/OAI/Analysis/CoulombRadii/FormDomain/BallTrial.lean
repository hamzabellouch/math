import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.RawThomasFermiEnergy
import OAI.Analysis.CoulombRadii.FieldAnalysis.UniformBall

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical SchwartzMap Pointwise
noncomputable section
namespace Coulomb

def ballKineticCoefficient : ℝ :=
  thomasFermiCoefficient*(4*Real.pi/3)/(4*Real.pi/3)^(5/3:ℝ)

lemma ballKineticCoefficient_pos : 0 < ballKineticCoefficient := by
  unfold ballKineticCoefficient thomasFermiCoefficient
  positivity

lemma ballCloud_power {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M) (y : Space) :
    thomasFermiCoefficient*(∫ x, ballCloud y a M x^(5/3:ℝ)) =
      ballKineticCoefficient*M^(5/3:ℝ)/a^2 := by
  unfold ballCloud
  rw [integral_sub_right_eq_self (fun x => uniformBall a M x^(5/3:ℝ)) y,uniformBall_power ha]
  have hc : 0 < 4*Real.pi/3 := by positivity
  rw [Real.div_rpow hM (by positivity),Real.mul_rpow hc.le (pow_nonneg ha.le 3)]
  have he : (a^3)^(5/3:ℝ) = a^5 := by
    rw [← Real.rpow_natCast a 3, ← Real.rpow_mul ha.le]
    norm_num
  rw [he]
  unfold ballKineticCoefficient
  field_simp [ha.ne', (Real.rpow_pos_of_pos hc (5/3:ℝ)).ne']

lemma ballCloud_rawTF_bound {J k : ℕ} (S : Nuclei J) (u : H1Vector k)
    {A : Set Space} (hu : SpatiallySupported u A)
    {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M) (y : Space)
    (hcore : ∀ z ∈ A, a ≤ ‖z-y‖) (hnuc : ∀ j, a ≤ ‖S.position j-y‖) :
    rawThomasFermiEnergy (coreScreenedField S u) (ballCloud y a M) ≤
      ballKineticCoefficient*M^(5/3:ℝ)/a^2-M*coreScreenedField S u y+(5/4:ℝ)*M^2/a := by
  unfold rawThomasFermiEnergy
  rw [ballCloud_power ha hM,coreScreenedField_ballCloud S u hu ha hM y hcore hnuc]
  calc
    _ ≤ ballKineticCoefficient*M^(5/3:ℝ)/a^2-M*coreScreenedField S u y+
        ((5/2:ℝ)*M^2/a)/2 := by
      have H := ballCloud_coulombBilinear_bound ha hM y
      linarith
    _ = _ := by ring

lemma ballCloud_support {a M : ℝ} (y z : Space) (hz : z ∉ Metric.closedBall y a) :
    ballCloud y a M z = 0 := by
  apply uniformBall_support
  simpa only [Metric.mem_closedBall,dist_eq_norm,not_le] using hz

lemma ballCloud_ne_zero_norm {a M : ℝ} (y z : Space) (hz : ballCloud y a M z ≠ 0) :
    ‖z-y‖ < a := by
  by_contra hn
  apply hz
  change (Metric.ball (0:Space) a).indicator (fun _ => M/(4*Real.pi/3*a^3)) (z-y) = 0
  exact Set.indicator_of_notMem (by simpa only [Metric.mem_ball,dist_zero_right] using hn) _

lemma ballCloud_separated_window {a : ℝ} (ha : 0 < a) (y : Space)
    (g : 𝓢(Space,ℝ)) (hgs : ∀ z, a < ‖z‖ → g z = 0)
    {A : Set Space} (hsep : ∀ z ∈ A, 3*a ≤ ‖z-y‖) :
    Disjoint A (Metric.closedBall y a + tsupport (g : Space → ℝ)) := by
  apply Set.disjoint_left.mpr
  rintro z hz ⟨v,hv,w,hw,rfl⟩
  have hw' : ‖w‖ ≤ a := by
    have H : tsupport (g : Space → ℝ) ⊆ Metric.closedBall 0 a := by
      apply closure_minimal ?_ Metric.isClosed_closedBall
      intro x hx
      simpa only [Metric.mem_closedBall,dist_zero_right] using
        (le_of_not_gt (fun h => hx (hgs x h)) : ‖x‖ ≤ a)
    simpa only [Metric.mem_closedBall,dist_zero_right] using H hw
  have hv' : ‖v-y‖ ≤ a := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hv
  have hnorm : ‖v+w-y‖ ≤ 2*a := by
    calc
      ‖v+w-y‖ = ‖(v-y)+w‖ := by congr 1; abel
      _ ≤ ‖v-y‖+‖w‖ := norm_add_le _ _
      _ ≤ 2*a := by linarith
  linarith [hsep (v+w) hz]

theorem ballCloud_trial {J k : ℕ} (S : Nuclei J) (u : H1Vector k)
    (hu : Antisymmetric u) (hmu : mass u = 1)
    (g : 𝓢(Space,ℝ)) (hg : (∫ x : Space, g x^2) = 1)
    (hgc : HasCompactSupport (g : Space → ℝ))
    (hrad : ∀ z, g z = g (EuclideanSpace.single 0 ‖z‖))
    {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M) (hgs : ∀ z, a < ‖z‖ → g z = 0)
    (y : Space) (A : Set Space) (hA : IsClosed A) (hsu : SpatiallySupported u A)
    (hcore : ∀ z ∈ A, 3*a ≤ ‖z-y‖) (hnuc : ∀ j, 3*a ≤ ‖S.position j-y‖) :
    unrestrictedFormBottom S ≤ ((form S u-M*coreScreenedField S u y+
      ballKineticCoefficient*M^(5/3:ℝ)/a^2 + (1/2:ℝ)*M*
      (∑ b : Fin 3, ∫ x : Space, (fderiv ℝ g x (EuclideanSpace.single b 1))^2)+
      (5/4:ℝ)*M^2/a : ℝ) : EReal) := by
  have hd : ∀ z x : Space, 3*a ≤ ‖z-y‖ → ballCloud y a M x ≠ 0 → a ≤ ‖z-x‖ := by
    intro z x hz hx
    have H := norm_sub_le_norm_sub_add_norm_sub z x y
    have hx' := ballCloud_ne_zero_norm y x hx
    linarith
  have H := source_free_trial_raw S u hu hmu g hg hgc hrad ha hgs (ballCloud y a M)
    (fun z => uniformBall_nonneg ha hM (z-y)) (ballCloud_measurable a M y)
    ((uniformBall_power_integrable a M).comp_sub_right y) (Metric.closedBall y a) A
    (isCompact_closedBall y a) hA (ballCloud_support y) hsu
    (ballCloud_separated_window ha y g hgs hcore)
    (fun z hz x hx => hd z x (hcore z hz) hx) (fun j x hx => hd (S.position j) x (hnuc j) hx)
  rw [ballCloud_mass ha] at H
  apply H.trans
  apply EReal.coe_le_coe_iff.mpr
  have HT := ballCloud_rawTF_bound S u hsu ha hM y
    (fun z hz => (by linarith [hcore z hz] : a ≤ ‖z-y‖))
    (fun j => (by linarith [hnuc j] : a ≤ ‖S.position j-y‖))
  linarith

end Coulomb
end

end
end

end OAI
