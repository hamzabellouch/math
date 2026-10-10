import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations
import Mathlib.MeasureTheory.Function.UniformIntegrable

namespace OAI

section

/-! # The product step for strongly convergent scalar velocity averages -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.Compactness

theorem tendstoInMeasure_mul {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsFiniteMeasure μ] {f g : ℕ → X → ℝ} {a b : X → ℝ}
    (hfm : ∀ n, AEStronglyMeasurable (f n) μ) (hgm : ∀ n, AEStronglyMeasurable (g n) μ)
    (hf : TendstoInMeasure μ f atTop a) (hg : TendstoInMeasure μ g atTop b) :
    TendstoInMeasure μ (fun n x => f n x*g n x) atTop (fun x => a x*b x) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff (fun n => (hfm n).mul (hgm n))).mpr
  intro ns hns
  obtain ⟨i,hi,hfi⟩ := (hf.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  obtain ⟨j,hj,hgj⟩ := (hg.comp (hns.comp hi).tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨i ∘ j,hi.comp hj,?_⟩
  filter_upwards [hfi,hgj] with x hfx hgx
  exact (hfx.comp hj.tendsto_atTop).mul hgx

theorem tendsto_L1_product {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsFiniteMeasure μ] {f g : ℕ → X → ℝ} {a b : X → ℝ}
    (hfm : ∀ n, AEStronglyMeasurable (f n) μ) (hgm : ∀ n, AEStronglyMeasurable (g n) μ)
    (hf : Tendsto (fun n => eLpNorm (fun x => f n x-a x) 1 μ) atTop (𝓝 0))
    (hg : Tendsto (fun n => eLpNorm (fun x => g n x-b x) 1 μ) atTop (𝓝 0))
    (hui : UniformIntegrable (fun n x => f n x*g n x) 1 μ) :
    Tendsto (fun n => eLpNorm (fun x => f n x*g n x-a x*b x) 1 μ) atTop (𝓝 0) := by
  have hfa : TendstoInMeasure μ f atTop a :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1:ℝ≥0∞) ≠ 0) hf
  have hgb : TendstoInMeasure μ g atTop b :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1:ℝ≥0∞) ≠ 0) hg
  have hm := tendstoInMeasure_mul hfm hgm hfa hgb
  exact tendsto_Lp_finite_of_tendstoInMeasure (by norm_num) (by norm_num)
    (fun n => (hfm n).mul (hgm n)) (hui.memLp_of_tendstoInMeasure hm) hui.1 hm

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Uniform bounds for velocity averages from an integrable velocity majorant -/

noncomputable section

open MeasureTheory Filter Set

namespace BoltzmannNonuniqueness.Compactness

theorem average_le_majorant {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    {f k : X × Y → ℝ} {M : Y → ℝ} (hM : Integrable M ν)
    (hM0 : ∀ y, 0 ≤ M y) {C : ℝ}
    (hC : 0 ≤ C) (hk : ∀ z, |k z| ≤ C)
    (hf : ∀ᵐ z ∂μ.prod ν, k z ≠ 0 → |f z| ≤ M z.2) :
    ∀ᵐ x ∂μ, |∫ y, k (x,y)*f (x,y) ∂ν| ≤ C*(∫ y, M y ∂ν) := by
  filter_upwards [Measure.ae_ae_of_ae_prod hf] with x hx
  have hb : ∀ᵐ y ∂ν, ‖k (x,y)*f (x,y)‖ ≤ C*M y := by
    filter_upwards [hx] with y hy
    by_cases hk0 : k (x,y) = 0
    · simp only [hk0,zero_mul,norm_zero]
      exact mul_nonneg hC (hM0 y)
    · rw [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul (hk (x,y)) (hy hk0) (abs_nonneg _) hC
  simpa only [Real.norm_eq_abs,integral_const_mul] using
    norm_integral_le_of_norm_le (hM.const_mul C) hb

end BoltzmannNonuniqueness.Compactness

end

end

end OAI
