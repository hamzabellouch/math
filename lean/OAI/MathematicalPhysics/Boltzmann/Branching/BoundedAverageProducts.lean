import OAI.MathematicalPhysics.Boltzmann.Approximation.CapHotSourceIntegrability
import OAI.MathematicalPhysics.Boltzmann.Branching.AverageMajorant
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedHotRegularity

namespace OAI

section

/-! # A bounded representative of a density divided by its positive mass -/
noncomputable section
open MeasureTheory
open scoped NNReal
namespace BoltzmannNonuniqueness.Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

def boundedQuotient (C : ℝ≥0) (A R : X → ℝ) (x : X) : ℝ :=
  max (-(C:ℝ)) (min (C:ℝ) (A x/R x))

theorem boundedQuotient_measurable (C : ℝ≥0) {A R : X → ℝ}
    (hA : Measurable A) (hR : Measurable R) : Measurable (boundedQuotient C A R) :=
  measurable_const.max (measurable_const.min (hA.div hR))

omit [MeasurableSpace X] in
theorem boundedQuotient_bound (C : ℝ≥0) (A R : X → ℝ) (x : X) :
    |boundedQuotient C A R x| ≤ C := by
  apply abs_le.mpr
  exact ⟨le_max_left _ _,max_le (by linarith [C.coe_nonneg]) (min_le_left _ _)⟩

theorem boundedQuotient_eq_ae (C : ℝ≥0) {A R : X → ℝ}
    (hR : ∀ x, 0 < R x) (hA : ∀ᵐ x ∂μ, |A x| ≤ C*R x) :
    A =ᵐ[μ] fun x => R x*boundedQuotient C A R x := by
  filter_upwards [hA] with x hx
  have hq : |A x/R x| ≤ C := by
    rw [abs_div,abs_of_pos (hR x)]
    exact (div_le_iff₀ (hR x)).mpr hx
  have hq' := abs_le.mp hq
  simp only [boundedQuotient,min_eq_right hq'.2,max_eq_right hq'.1]
  field_simp [(hR x).ne']

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Multiplying strongly convergent averages with eventual common bounds -/

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness.Compactness

theorem tendsto_L1_product_of_eventually_bounded {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {f g : ℕ → X → ℝ} {a b : X → ℝ}
    (hfm : ∀ n, AEStronglyMeasurable (f n) μ) (hgm : ∀ n, AEStronglyMeasurable (g n) μ)
    (hf : Tendsto (fun n => eLpNorm (fun x => f n x-a x) 1 μ) atTop (𝓝 0))
    (hg : Tendsto (fun n => eLpNorm (fun x => g n x-b x) 1 μ) atTop (𝓝 0))
    {C D : ℝ} (hC : 0 ≤ C)
    (hfb : ∀ᶠ n in atTop, ∀ᵐ x ∂μ, |f n x| ≤ C)
    (hgb : ∀ᶠ n in atTop, ∀ᵐ x ∂μ, |g n x| ≤ D) :
    Tendsto (fun n => eLpNorm (fun x => f n x*g n x-a x*b x) 1 μ) atTop (𝓝 0) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hfb.and hgb)
  have hui : UniformIntegrable (fun n x => f (n+N) x*g (n+N) x) 1 μ := by
    apply uniformIntegrable_of_abs_le (integrable_const (C*D))
      (fun n => (hfm (n+N)).mul (hgm (n+N)))
    intro n
    obtain ⟨hnf,hng⟩ := hN (n+N) (Nat.le_add_left N n)
    filter_upwards [hnf,hng] with x hfx hgx
    change |f (n+N) x*g (n+N) x| ≤ C*D
    rw [abs_mul]
    exact mul_le_mul hfx hgx (abs_nonneg _) hC
  have h := tendsto_L1_product (fun n => hfm (n+N)) (fun n => hgm (n+N))
    (hf.comp (tendsto_add_atTop_nat N)) (hg.comp (tendsto_add_atTop_nat N)) hui
  exact (tendsto_add_atTop_iff_nat N).mp h

end BoltzmannNonuniqueness.Compactness

end

end

end OAI
