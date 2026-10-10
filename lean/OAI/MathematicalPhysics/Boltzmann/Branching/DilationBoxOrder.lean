import OAI.MathematicalPhysics.Boltzmann.Compactness.KineticDilationIntegral
import OAI.MathematicalPhysics.Boltzmann.Branching.SeparationBoxContainment

namespace OAI

/-! # Positive mass comparison under a second bounded dilation -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.JetCopyDatum

theorem kineticDilation_mul (r s : ℝ) (z : Published.KineticPhase) :
    kineticDilation r (kineticDilation s z) = kineticDilation (r*s) z := by
  ext <;> simp [kineticDilation,smul_smul,mul_assoc]

theorem dilation_awayBox_subset {r A R ε : ℝ} {j : ℕ} (hr : 0 < r)
    (ht : r*A ≤ 1) (hx : r*R ≤ (j:ℝ)+1) (hv : R ≤ (j:ℝ)+1)
    (hε : 1/((j:ℝ)+1) ≤ ε) :
    kineticDilation r⁻¹ ⁻¹' awayKineticBox A R ε ⊆ separationBox j := by
  intro z hz
  have hh : kineticDilation r (kineticDilation r⁻¹ z) = z := by
    rw [kineticDilation_mul,mul_inv_cancel₀ hr.ne']
    simp [kineticDilation]
  rw [← hh]
  let w := kineticDilation r⁻¹ z
  change w ∈ awayKineticBox A R ε at hz
  change kineticDilation r w ∈ separationBox j
  have hnx : ‖w.1.2‖ ≤ R := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz.1.1.2
  have hnv : ‖w.2‖ ≤ R := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz.1.2
  refine ⟨⟨⟨⟨mul_nonneg hr.le hz.1.1.1.1,
    (mul_le_mul_of_nonneg_left hz.1.1.1.2 hr.le).trans ht⟩,?_⟩,?_⟩,?_⟩
  · change dist (r • w.1.2) 0 ≤ (j:ℝ)+1
    rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    exact (mul_le_mul_of_nonneg_left hnx hr.le).trans hx
  · simpa only [Metric.mem_closedBall,dist_zero_right,kineticDilation] using hnv.trans hv
  · exact hε.trans hz.2

theorem dilation_box_mass_le {r A R ε : ℝ} {j : ℕ} (hr : 0 < r)
    (ht : r*A ≤ 1) (hx : r*R ≤ (j:ℝ)+1) (hv : R ≤ (j:ℝ)+1)
    (hε : 1/((j:ℝ)+1) ≤ ε) {f : Published.KineticPhase → ℝ}
    (hf : IntegrableOn f (separationBox j)) (hn : ∀ z, 0 ≤ f z) :
    (∫ z in awayKineticBox A R ε, r⁻¹*f (kineticDilation r z)) ≤
      (r^5)⁻¹ * ∫ z in separationBox j, f z := by
  rw [scaled_setIntegral hr (measurableSet_awayKineticBox A R ε)]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (pow_nonneg hr.le 5))
  exact setIntegral_mono_set hf (ae_of_all _ hn)
    (Filter.Eventually.of_forall (dilation_awayBox_subset hr ht hx hv hε))

end BoltzmannNonuniqueness.JetCopyDatum

end

end OAI
