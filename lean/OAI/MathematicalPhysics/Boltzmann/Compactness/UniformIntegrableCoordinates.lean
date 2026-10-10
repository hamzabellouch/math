import OAI.MathematicalPhysics.Boltzmann.Compactness.KineticWindowL1
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakTimeSurvival

namespace OAI

section

/-! # A vanishing uniform bound controls the integral on a finite measure space -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BoltzmannNonuniqueness

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem integral_abs_tendsto_of_uniform_bound {f : ℕ → X → ℝ} {b : ℕ → ℝ}
    (hm : ∀ n, AEStronglyMeasurable (f n) μ)
    (hb : ∀ᶠ n in atTop, ∀ᵐ x ∂μ, |f n x| ≤ b n)
    (hlim : Tendsto b atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, |f n x| ∂μ) atTop (𝓝 0) := by
  have hi : ∀ᶠ n in atTop, (∫ x, |f n x| ∂μ) ≤ (μ univ).toReal*b n := by
    filter_upwards [hb] with n hn
    have hf : Integrable (f n) μ := (integrable_const (b n)).mono' (hm n)
      (by simpa only [Real.norm_eq_abs] using hn)
    have ha : Integrable (fun x => |f n x|) μ := by
      simpa only [Real.norm_eq_abs] using hf.norm
    calc
      _ ≤ ∫ _ : X, b n ∂μ := integral_mono_ae ha (integrable_const _) hn
      _ = _ := by
        simp only [integral_const,smul_eq_mul]
        rfl
  apply squeeze_zero' (Eventually.of_forall (fun n => integral_nonneg (fun x => abs_nonneg _))) hi
  simpa only [mul_zero] using hlim.const_mul (μ univ).toReal

end BoltzmannNonuniqueness

end

end

section

/-! # Uniform integrability under the coordinate and bounded-weight changes -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal
namespace BoltzmannNonuniqueness.Published

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y}

theorem eLpNorm_comp_equiv_restrict (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν)
    {E : Type*} [NormedAddCommGroup E] (f : Y → E) (S : Set X) :
    eLpNorm (f ∘ e) 1 (μ.restrict S) = eLpNorm f 1 (ν.restrict (e '' S)) := by
  have hm : Measure.map e (μ.restrict S) = ν.restrict (e '' S) := by
    rw [← he.map_eq,e.restrict_map,preimage_image_eq _ e.injective]
  rw [← hm]
  exact e.measurableEmbedding.eLpNorm_map_measure.symm

theorem uniformIntegrable_comp_equiv (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν)
    (f : ℕ → Y → ℝ) (hf : UniformIntegrable f 1 ν) :
    UniformIntegrable (fun n => f n ∘ e) 1 μ := by
  constructor
  · rw [unifIntegrable_iff]
    intro ε hε
    obtain ⟨δ,hδ,hd⟩ := unifIntegrable_iff.mp hf.1 ε hε
    refine ⟨δ,hδ,fun n S hS => ?_⟩
    rw [eLpNorm_comp_equiv_restrict e he]
    apply hd n (e '' S)
    have hm := he.measure_preimage_emb e.measurableEmbedding (e '' S)
    rw [← hm,preimage_image_eq _ e.injective]
    exact hS
  · obtain ⟨C,hC⟩ := hf.2
    refine ⟨C,fun n => ?_⟩
    rw [eLpNorm_comp_measurePreserving (hf.aestronglyMeasurable n) he]
    exact hC n

theorem uniformIntegrable_norm_domination (f : ℕ → X → ℝ) (g : ℕ → X → ℂ)
    (hf : UniformIntegrable f 1 μ) (hg : ∀ n, Measurable (g n))
    (D : ℝ≥0) (hd : ∀ n x, ‖g n x‖ ≤ (D : ℝ)*‖f n x‖) :
    UniformIntegrable g 1 μ := by
  have hnorm n (S : Set X) : eLpNorm (g n) 1 (μ.restrict S) ≤
      (D : ℝ≥0∞)*eLpNorm (f n) 1 (μ.restrict S) := by
    simpa only [ENNReal.ofReal_coe_nnreal] using
      eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hg n).aestronglyMeasurable.restrict
        (ae_of_all _ (hd n)) 1
  constructor
  · have ht := ENNReal.Tendsto.const_mul hf.1 (Or.inr (show (D : ℝ≥0∞) ≠ ⊤ from ENNReal.coe_ne_top))
    change Tendsto _ (𝓝 0) (𝓝 0)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [mul_zero,bot_eq_zero] using ht) (fun _ => bot_le)
    intro δ
    simp only [iSup_le_iff]
    intro n S hS
    apply (hnorm n S).trans
    gcongr
    exact le_iSup_of_le n (le_iSup_of_le S (le_iSup_of_le hS le_rfl))
  · obtain ⟨C,hC⟩ := hf.2
    refine ⟨D*C,fun n => ?_⟩
    have h := hnorm n Set.univ
    simp only [Measure.restrict_univ] at h
    apply h.trans
    rw [ENNReal.coe_mul]
    gcongr
    exact hC n

end BoltzmannNonuniqueness.Published

end

end

end OAI
