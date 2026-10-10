import OAI.MathematicalPhysics.Boltzmann.Approximation.MassNormalizedCollisionLimits
import OAI.MathematicalPhysics.Boltzmann.Branching.InMeasureDifference

namespace OAI

/-! # Removing a spatial-mass normalizer from a uniformly integrable residual -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem unitNormalized_residual_L1
    {e u r : ℕ → X → ℝ} {s : X → ℝ}
    (hem : ∀ n, Measurable (e n)) (hum : ∀ n, Measurable (u n))
    (hrm : ∀ n, Measurable (r n)) (hu : ∀ n x, 0 ≤ u n x)
    (hr : ∀ n x, 0 ≤ r n x) (hs : ∀ x, 0 ≤ s x)
    (hrt : Tendsto (fun n => eLpNorm (fun x => r n x-s x) 1 μ) atTop (𝓝 0))
    (het : Tendsto (fun n => eLpNorm (fun x => e n x/(1+r n x)) 1 μ) atTop (𝓝 0))
    (hui : UniformIntegrable (fun n x => e n x/(1+u n x)) 1 μ) :
    Tendsto (fun n => eLpNorm (fun x => e n x/(1+u n x)) 1 μ) atTop (𝓝 0) := by
  have he0 : Tendsto (fun n => eLpNorm (fun x =>
      e n x/(1+r n x)-(0:ℝ)/(1+s x)) 1 μ) atTop (𝓝 0) := by
    simpa only [zero_div,sub_zero] using het
  have he := tendstoInMeasure_of_strong_massNormalized hem hrm hr hs hrt he0
  have hd : TendstoInMeasure μ (fun n x => e n x/(1+u n x)) atTop (fun _ => 0) := by
    apply tendstoInMeasure_zero_of_abs_le he
    intro n x
    rw [abs_div,abs_of_nonneg (show 0 ≤ 1+u n x by linarith [hu n x])]
    exact div_le_self (abs_nonneg _) (by linarith [hu n x])
  have hm n : AEStronglyMeasurable (fun x => e n x/(1+u n x)) μ :=
    ((hem n).div (measurable_const.add (hum n))).aestronglyMeasurable
  have h := tendsto_Lp_finite_of_tendstoInMeasure (by norm_num) (by norm_num)
    hm (hui.memLp_of_tendstoInMeasure hd) hui.1 hd
  apply h.congr'
  exact Eventually.of_forall (fun n => eLpNorm_congr_ae (ae_of_all _ (fun _ => sub_zero _)))

end BoltzmannNonuniqueness.Compactness

end

end OAI
