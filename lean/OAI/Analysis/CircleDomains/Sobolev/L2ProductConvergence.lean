import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! Strong L² convergence may be paired with uniformly bounded,
almost-everywhere convergent multipliers and a fixed L² test. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem abs_integral_mul_le_eLpNorm_two
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {f g : X → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, f x * g x ∂μ| ≤ (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal := by
  have he : (∫ x, f x * g x ∂μ) = inner ℝ (hf.toLp f) (hg.toLp g) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
    simp only [Real.inner_apply, hx, hy]
  rw [he, ← Lp.norm_toLp, ← Lp.norm_toLp]
  exact abs_real_inner_le_norm _ _

 theorem tendsto_integral_bounded_mul_L2
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {g : ℕ → X → ℝ} {G : X → ℝ} {h : ℕ → X → ℝ} {H φ : X → ℝ}
    (hg : ∀ n, MemLp (g n) 2 μ) (hG : MemLp G 2 μ) (hφ : MemLp φ 2 μ)
    (hl : Tendsto (fun n => eLpNorm (fun x => g n x - G x) 2 μ) atTop (𝓝 0))
    (hm : ∀ n, AEStronglyMeasurable (h n) μ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ n, ∀ᵐ x ∂μ, ‖h n x‖ ≤ C)
    (hp : ∀ᵐ x ∂μ, Tendsto (fun n => h n x) atTop (𝓝 (H x))) :
    Tendsto (fun n => ∫ x, h n x * g n x * φ x ∂μ) atTop
      (𝓝 (∫ x, H x * G x * φ x ∂μ)) := by
  have hH : AEStronglyMeasurable H μ := aestronglyMeasurable_of_tendsto_ae atTop hm hp
  have hHb : ∀ᵐ x ∂μ, ‖H x‖ ≤ C := by
    filter_upwards [hp, ae_all_iff.2 hb] with x hx hb
    exact le_of_tendsto hx.norm (Eventually.of_forall hb)
  have hprod : Integrable (fun x => G x * φ x) μ := hG.integrable_mul hφ
  have hdom : Integrable (fun x => C * ‖G x * φ x‖) μ := hprod.norm.const_mul C
  have hmain := tendsto_integral_of_dominated_convergence
    (F := fun n x => h n x * G x * φ x) (f := fun x => H x * G x * φ x)
    (fun x => C * ‖G x * φ x‖)
    (fun n => ((hm n).mul hG.aestronglyMeasurable).mul hφ.aestronglyMeasurable)
    hdom (fun n => by
      filter_upwards [hb n] with x hx
      simpa only [norm_mul, mul_assoc] using
        mul_le_mul_of_nonneg_right hx (norm_nonneg (G x * φ x)))
    (by filter_upwards [hp] with x hx; exact (hx.mul_const _).mul_const _)
  have herr : Tendsto (fun n => ∫ x, h n x * (g n x - G x) * φ x ∂μ)
      atTop (𝓝 0) := by
    have hnorm : Tendsto (fun n => (eLpNorm (fun x => g n x - G x) 2 μ).toReal)
        atTop (𝓝 0) := by
      simpa only [Function.comp_def, ENNReal.toReal_zero] using
        (ENNReal.tendsto_toReal (by simp)).comp hl
    apply squeeze_zero_norm' _ (by
      simpa using ((hnorm.const_mul C).mul_const (eLpNorm φ 2 μ).toReal))
    apply Eventually.of_forall
    intro n
    let D : X → ℝ := fun x => g n x - G x
    have hD : MemLp D 2 μ := (hg n).sub hG
    have hint : Integrable (fun x => ‖D x‖ * ‖φ x‖) μ := hD.norm.integrable_mul hφ.norm
    calc
      ‖∫ x, h n x * D x * φ x ∂μ‖ ≤ ∫ x, ‖h n x * D x * φ x‖ ∂μ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ x, C * (‖D x‖ * ‖φ x‖) ∂μ := by
        apply integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _)
          (hint.const_mul C)
        filter_upwards [hb n] with x hx
        simpa only [norm_mul, mul_assoc] using
          mul_le_mul_of_nonneg_right hx (mul_nonneg (norm_nonneg (D x)) (norm_nonneg (φ x)))
      _ = C * ∫ x, ‖D x‖ * ‖φ x‖ ∂μ := integral_const_mul _ _
      _ ≤ C * ((eLpNorm D 2 μ).toReal * (eLpNorm φ 2 μ).toReal) := by
        apply mul_le_mul_of_nonneg_left _ hC
        have ha := abs_integral_mul_le_eLpNorm_two hD.norm hφ.norm
        have hn : 0 ≤ ∫ x, ‖D x‖ * ‖φ x‖ ∂μ := integral_nonneg
          (fun x => mul_nonneg (norm_nonneg (D x)) (norm_nonneg (φ x)))
        rw [eLpNorm_norm _ hD.aestronglyMeasurable,
          eLpNorm_norm _ hφ.aestronglyMeasurable, abs_of_nonneg hn] at ha
        exact ha
      _ = C * (eLpNorm D 2 μ).toReal * (eLpNorm φ 2 μ).toReal := by ring
  have hsum := herr.add hmain
  simp only [zero_add] at hsum
  convert hsum using 1
  funext n
  have hfirst : Integrable (fun x => h n x * (g n x - G x) * φ x) μ := by
    apply ( ((hg n).sub hG).integrable_mul hφ).norm.const_mul C |>.mono'
      (((hm n).mul ((hg n).sub hG).aestronglyMeasurable).mul hφ.aestronglyMeasurable)
    filter_upwards [hb n] with x hx
    change ‖h n x * (g n x - G x) * φ x‖ ≤ C * ‖(g n x - G x) * φ x‖
    simpa only [norm_mul, mul_assoc] using
      mul_le_mul_of_nonneg_right hx (norm_nonneg ((g n x - G x) * φ x))
  have hsecond : Integrable (fun x => h n x * G x * φ x) μ := by
    apply hdom.mono' (((hm n).mul hG.aestronglyMeasurable).mul hφ.aestronglyMeasurable)
    filter_upwards [hb n] with x hx
    change ‖h n x * G x * φ x‖ ≤ C * ‖G x * φ x‖
    simpa only [norm_mul, mul_assoc] using
      mul_le_mul_of_nonneg_right hx (norm_nonneg (G x * φ x))
  rw [← integral_add hfirst hsecond]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by ring

end CircleDomainRigidity

end

end OAI
