import OAI.MathematicalPhysics.Boltzmann.Approximation.CapDilationCompactness
import OAI.MathematicalPhysics.Boltzmann.Approximation.DormantBoxLimit

namespace OAI

section

/-! # Countably many bounded boxes for the final separation argument -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.JetCopyDatum

def separationBox (j : ℕ) : Set Published.KineticPhase :=
  awayKineticBox 1 (j+1) (1/((j:ℝ)+1))

theorem measurableSet_separationBox (j : ℕ) : MeasurableSet (separationBox j) :=
  measurableSet_awayKineticBox _ _ _

def scaledBoxMass (r : ℝ) (f : Published.KineticPhase → ℝ) (j : ℕ) : ℝ :=
  ∫ z in separationBox j, r⁻¹*f (kineticDilation r z)

theorem shrinking_separationBox_in_cell {τ : ℝ} (hτ : 0 < τ) (hτmax : τ ≤ 1/32)
    {n j : ℕ} (hj : j ≤ n) :
    kineticDilation (shrinkingHorizon τ n)⁻¹ ⁻¹' separationBox j ⊆
      TorusKineticChart.region (shrinkingHorizon τ n) := by
  intro z hz
  let r := shrinkingHorizon τ n
  have hr : 0 < r := shrinkingHorizon_pos hτ n
  have hbox : kineticDilation r⁻¹ z ∈ separationBox j := hz
  have htx : 0 ≤ r⁻¹*z.1.1 ∧ r⁻¹*z.1.1 ≤ 1 := hbox.1.1.1
  have hx : ‖r⁻¹ • z.1.2‖ ≤ (j:ℝ)+1 := by
    simpa only [Metric.mem_closedBall,dist_zero_right,kineticDilation] using hbox.1.1.2
  have hx' : ‖z.1.2‖ ≤ r*((j:ℝ)+1) := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)] at hx
    have hh := mul_le_mul_of_nonneg_left hx hr.le
    simpa only [← mul_assoc,mul_inv_cancel₀ hr.ne',one_mul] using hh
  have hscale : r*((j:ℝ)+1) ≤ τ := by
    dsimp [r,shrinkingHorizon]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < (n:ℝ)+1)).mpr
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.add_le_add_right hj 1) hτ.le
  have ht : z.1.1 ∈ Icc 0 r := by
    have h0 := mul_le_mul_of_nonneg_left htx.1 hr.le
    have h1 := mul_le_mul_of_nonneg_left htx.2 hr.le
    simp only [mul_zero,mul_one,← mul_assoc,mul_inv_cancel₀ hr.ne',one_mul] at h0 h1
    exact ⟨h0,h1⟩
  exact ⟨⟨ht,norm_quarter_mem_cube (hx'.trans (hscale.trans (hτmax.trans (by norm_num))))⟩,mem_univ _⟩

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Every bounded off-axis region fits in a fixed separation box -/
noncomputable section
open Set
namespace BoltzmannNonuniqueness.JetCopyDatum

theorem exists_separationBox_parameters {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ j : ℕ, 2*R ≤ (j:ℝ)+1 ∧ R ≤ (j:ℝ)+1 ∧ 1/((j:ℝ)+1) ≤ ε := by
  obtain ⟨j,hj⟩ := exists_nat_gt (max (2*R) (1/ε))
  have h1 : 2*R ≤ (j:ℝ)+1 := by linarith [le_max_left (2*R) (1/ε)]
  have h2 : 1/ε ≤ (j:ℝ)+1 := by linarith [le_max_right (2*R) (1/ε)]
  refine ⟨j,h1,(show R ≤ 2*R by linarith only [hR]).trans h1,?_⟩
  apply (div_le_iff₀ (by positivity : 0 < (j:ℝ)+1)).mpr
  have h := (div_le_iff₀ hε).mp h2
  nlinarith

theorem awayKineticBox_subset_separationBox {A R ε : ℝ} {j : ℕ} (hA : A ≤ 1)
    (hR : R ≤ (j:ℝ)+1) (hε : 1/((j:ℝ)+1) ≤ ε) :
    awayKineticBox A R ε ⊆ separationBox j := by
  intro z hz
  exact ⟨⟨⟨⟨hz.1.1.1.1,hz.1.1.1.2.trans hA⟩,Metric.closedBall_subset_closedBall hR hz.1.1.2⟩,
    Metric.closedBall_subset_closedBall hR hz.1.2⟩,hε.trans hz.2⟩

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
