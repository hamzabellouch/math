import Mathlib.MeasureTheory.Function.UnifTight
import OAI.MathematicalPhysics.Boltzmann.Jets.SpatialCutoffIntegrability

namespace OAI

/-! # Uniform L¹ approximation preserves tightness on infinite measure spaces -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.Compactness

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem unifTight_of_approximation {f : ℕ → X → ℝ} {g : ℕ → ℕ → X → ℝ}
    (hg : ∀ j, UnifTight (g j) 1 μ)
    (happrox : ∀ ε : ℝ≥0∞, 0 < ε → ∃ j : ℕ, ∀ n,
      eLpNorm (fun x => f n x-g j n x) 1 μ ≤ ε) : UnifTight f 1 μ := by
  intro ε hε
  obtain ⟨j,hj⟩ := happrox (ε/2) (ε.half_pos hε.ne')
  obtain ⟨s,hs,hμs,hgs⟩ := (hg j).exists_measurableSet_indicator (ε.half_pos hε.ne').ne'
  refine ⟨s,hμs.ne,fun n => ?_⟩
  have he : sᶜ.indicator (f n) =
      sᶜ.indicator (fun x => f n x-g j n x)+sᶜ.indicator (g j n) := by
    ext x
    by_cases hx : x ∈ s <;> simp [hx]
  rw [he]
  calc
    _ ≤ eLpNorm (sᶜ.indicator (fun x => f n x-g j n x)) 1 μ+
        eLpNorm (sᶜ.indicator (g j n)) 1 μ := eLpNorm_add_le (by norm_num)
    _ ≤ ε/2+ε/2 := add_le_add ((eLpNorm_indicator_le _ hs.compl).trans (hj n)) (hgs n)
    _ = ε := ε.add_halves

theorem unifTight_mono {f g : ℕ → X → ℝ}
    (hg : UnifTight g 1 μ) (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hle : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ₑ ≤ ‖g n x‖ₑ) : UnifTight f 1 μ := by
  intro ε hε
  obtain ⟨s,hs,hμs,hgs⟩ := hg.exists_measurableSet_indicator hε.ne'
  refine ⟨s,hμs.ne,fun n => ?_⟩
  apply le_trans (eLpNorm_mono_enorm_ae ((hf n).indicator hs.compl) ?_) (hgs n)
  filter_upwards [hle n] with x hx
  by_cases hxs : x ∈ s
  · simp only [indicator_of_notMem (show x ∉ sᶜ from fun h => h hxs)]
    exact le_rfl
  · simpa only [indicator_of_mem (show x ∈ sᶜ from hxs)] using hx

theorem unifTight_of_integrable_majorant {f : ℕ → X → ℝ} {g : X → ℝ}
    (hg : Integrable g μ) (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hle : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ₑ ≤ ‖g x‖ₑ) : UnifTight f 1 μ :=
  unifTight_mono (unifTight_const (by norm_num) (memLp_one_iff_integrable.mpr hg)) hf hle

variable {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} [SFinite ν]

theorem unifTight_of_spatial_cutoffs {f : ℕ → X × Y → ℝ}
    {G : X → ℝ≥0∞} {S : ℕ → Set X}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n z, 0 ≤ f n z)
    (hS : ∀ j, MeasurableSet (S j))
    (hG : ∀ n, ∀ᵐ x ∂μ, (∫⁻ y, ENNReal.ofReal (f n (x,y)) ∂ν) ≤ G x)
    (hout : ∀ j, UnifTight (fun n => outerCutoff (S j) (f n)) 1 (μ.prod ν))
    (hsmall : Tendsto (fun j => ∫⁻ x in S j, G x ∂μ) atTop (𝓝 0)) :
    UnifTight f 1 (μ.prod ν) := by
  apply unifTight_of_approximation hout
  intro ε hε
  have hev : ∀ᶠ j in atTop, (∫⁻ x in S j, G x ∂μ) ≤ ε :=
    (hsmall.eventually (gt_mem_nhds hε)).mono (fun _ h => h.le)
  obtain ⟨j,hj⟩ := hev.exists
  exact ⟨j,fun n => (spatial_cutoff_error (hfm n) (hf n) (hS j) (hG n)).trans hj⟩

end BoltzmannNonuniqueness.Compactness

end

end OAI
