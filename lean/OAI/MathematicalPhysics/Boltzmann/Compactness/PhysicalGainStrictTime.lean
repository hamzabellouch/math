import OAI.MathematicalPhysics.Boltzmann.Compactness.FiniteEntryPhaseBound
import OAI.MathematicalPhysics.Boltzmann.Compactness.LocalizedBlockComparison
import OAI.MathematicalPhysics.Boltzmann.Compactness.PhysicalEvolution

namespace OAI

section

/-! # Almost every finite physical history stays in its explicit reachable region -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory
namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem finiteFlightCone_wait {N n : ℕ} {h R : ℝ} {x : V}
    {p : PhysicalFlightState} (hq : finiteFlightCone N n h R x p)
    {s : ℝ} (hs : s ∈ Icc 0 p.1) :
    finiteFlightCone N n h R x (physicalAdvance p s) := by
  have hv : ‖p.2.2‖ ≤ R+2*N := by
    have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
    linarith [hq.2.2.1]
  refine ⟨sub_nonneg.mpr hs.2,by dsimp [physicalAdvance]; linarith [hq.2.1,hs.1],hq.2.2.1,?_⟩
  change ‖p.2.1+s • p.2.2-x‖ ≤ (h-(p.1-s))*(R+2*N)
  calc
    _ = ‖(p.2.1-x)+s • p.2.2‖ := by congr 1; module
    _ ≤ ‖p.2.1-x‖+‖s • p.2.2‖ := norm_add_le _ _
    _ = ‖p.2.1-x‖+s*‖p.2.2‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hs.1]
    _ ≤ (h-p.1)*(R+2*N)+s*(R+2*N) :=
      add_le_add hq.2.2.2 (mul_le_mul_of_nonneg_left hv hs.1)
    _ = _ := by ring

theorem physicalWaitingKernel_ae_finiteCone {N n : ℕ} {h R : ℝ} {x : V}
    (C : ℝ≥0) {p : PhysicalFlightState} (hq : finiteFlightCone N n h R x p) :
    ∀ᵐ q ∂physicalWaitingKernel C p, finiteFlightCone N n h R x q := by
  let A := {q | ¬finiteFlightCone N n h R x q}
  have hA : MeasurableSet A := (finiteFlightCone_measurable N n h R x).compl
  rw [ae_iff]
  change physicalWaitingKernel C p A = 0
  rw [← lintegral_indicator_one hA,physicalWaitingKernel_lintegral C p (F := A.indicator 1)
    (measurable_const.indicator hA)]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  have hz : A.indicator (1 : PhysicalFlightState → ℝ≥0∞) (physicalAdvance p s) = 0 := by
    apply indicator_of_notMem
    exact fun h => h (finiteFlightCone_wait hq ⟨hs.1.le,hs.2⟩)
  simp only [hz,mul_zero,Pi.zero_apply]

theorem physicalBeamCollision_ae_finiteCone {N n : ℕ} {h R : ℝ} {x : V}
    (b : BeamCoefficients) (T : ℝ) {p : PhysicalFlightState}
    (hq : finiteFlightCone N (n+1) h R x p)
    (hp : ‖b.plusPartner (T-p.1,p.2.1)‖ ≤ 2)
    (hm : ‖b.minusPartner (T-p.1,p.2.1)‖ ≤ 2) :
    ∀ᵐ q ∂physicalBeamCollision b T p, finiteFlightCone N n h R x q := by
  let A := {q | ¬finiteFlightCone N n h R x q}
  have hA : MeasurableSet A := (finiteFlightCone_measurable N n h R x).compl
  have hz (m : HistoryMark) (z : Sphere) :
      A.indicator (1 : PhysicalFlightState → ℝ≥0∞)
        (p.1,(p.2.1,markedChild m p.2.2 (b.plusPartner (T-p.1,p.2.1))
          (b.minusPartner (T-p.1,p.2.1)) z.1)) = 0 := by
    apply indicator_of_notMem
    intro hnot
    apply hnot
    simpa only [mediumParameterState,mediumPoint,sub_zero,add_zero,zero_smul] using
      finiteFlightCone_parameter_step b T hq m ⟨le_rfl,hq.1⟩ z
        (by simpa only [mediumPoint,add_zero,zero_smul] using hp)
        (by simpa only [mediumPoint,add_zero,zero_smul] using hm)
  rw [ae_iff]
  change physicalBeamCollision b T p A = 0
  rw [← lintegral_indicator_one hA,physicalBeamCollision_lintegral,
    physicalMarkedCollision_lintegral b T 1 p (F := A.indicator 1) (measurable_const.indicator hA),
    physicalMarkedCollision_lintegral b T 2 p (F := A.indicator 1) (measurable_const.indicator hA)]
  simp only [hz,lintegral_zero,mul_zero,add_zero]

theorem physicalBeamEvent_ae_finiteCone {N n : ℕ} {h R : ℝ} {x : V}
    (b : BeamCoefficients) (T : ℝ) (C : ℝ≥0) {p : PhysicalFlightState}
    (hq : finiteFlightCone N (n+1) h R x p)
    (hp : ∀ q, finiteFlightCone N (n+1) h R x q → ‖b.plusPartner (T-q.1,q.2.1)‖ ≤ 2)
    (hm : ∀ q, finiteFlightCone N (n+1) h R x q → ‖b.minusPartner (T-q.1,q.2.1)‖ ≤ 2) :
    ∀ᵐ q ∂physicalBeamEvent b T C p, finiteFlightCone N n h R x q := by
  apply Kernel.ae_comp_of_ae_ae (finiteFlightCone_measurable N n h R x)
  filter_upwards [physicalWaitingKernel_ae_finiteCone C hq] with q hq'
  exact physicalBeamCollision_ae_finiteCone b T hq' (hp q hq') (hm q hq')

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Positive physical gain histories use the open-left collision-time window -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory
namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem physicalBeamCollision_ae_fixed (b : BeamCoefficients) (T : ℝ)
    (p : PhysicalFlightState) :
    ∀ᵐ q ∂physicalBeamCollision b T p, q.1 = p.1 ∧ q.2.1 = p.2.1 := by
  let A := {q : PhysicalFlightState | ¬(q.1 = p.1 ∧ q.2.1 = p.2.1)}
  have hA : MeasurableSet A := by dsimp [A]; measurability
  have hz (v : V) : A.indicator (1 : PhysicalFlightState → ℝ≥0∞) (p.1,(p.2.1,v)) = 0 := by
    apply indicator_of_notMem
    simp [A]
  rw [ae_iff]
  change physicalBeamCollision b T p A = 0
  rw [← lintegral_indicator_one hA,physicalBeamCollision_lintegral,
    physicalMarkedCollision_lintegral b T 1 p (F := A.indicator 1) (measurable_const.indicator hA),
    physicalMarkedCollision_lintegral b T 2 p (F := A.indicator 1) (measurable_const.indicator hA)]
  simp only [hz,lintegral_zero,mul_zero,add_zero]

theorem physicalWaitingKernel_ae_remaining (C : ℝ≥0) (p : PhysicalFlightState) :
    ∀ᵐ q ∂physicalWaitingKernel C p, 0 ≤ q.1 ∧ q.1 < p.1 := by
  let A := {q : PhysicalFlightState | ¬(0 ≤ q.1 ∧ q.1 < p.1)}
  have hA : MeasurableSet A := by dsimp [A]; measurability
  rw [ae_iff]
  change physicalWaitingKernel C p A = 0
  rw [← lintegral_indicator_one hA,physicalWaitingKernel_lintegral C p (F := A.indicator 1)
    (measurable_const.indicator hA)]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  have hz : A.indicator (1 : PhysicalFlightState → ℝ≥0∞) (physicalAdvance p s) = 0 := by
    apply indicator_of_notMem
    change ¬¬(0 ≤ p.1-s ∧ p.1-s < p.1)
    exact not_not.mpr ⟨sub_nonneg.mpr hs.2,by linarith [hs.1]⟩
  simp only [hz,mul_zero,Pi.zero_apply]

theorem physicalBeamEvent_ae_time_window (b : BeamCoefficients) (T h : ℝ)
    (C : ℝ≥0) {p : PhysicalFlightState} (hp : p.1 ≤ h) :
    ∀ᵐ q ∂physicalBeamEvent b T C p, q ∈ physicalCollisionWindow (T-h) T := by
  apply Kernel.ae_comp_of_ae_ae (physicalCollisionWindow_measurable (T-h) T)
  filter_upwards [physicalWaitingKernel_ae_remaining C p] with q hq
  filter_upwards [physicalBeamCollision_ae_fixed b T q] with r hr
  rw [hr.1]
  exact ⟨by linarith [hq.2],by linarith [hq.1]⟩

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
