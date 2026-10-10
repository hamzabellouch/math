import OAI.GroupTheory.PolycyclicRecognition.Analysis.CocycleHaarAverage
import Mathlib.Topology.Algebra.Support

namespace OAI

/-! # Controlled scalar averages turn sublinear cocycles into coboundaries

The geometric data are compactly supported probability densities with
translation error of order inverse scale and support of order scale.
They contain no representation or cohomology hypotheses.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Filter

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]

structure ControlledReiterFamily (μ : Measure G) (length : G → ℝ) where
  scale : ℕ → ℝ
  scale_pos : ∀ n, 0 < scale n
  scale_tendsto : Tendsto scale atTop atTop
  weight : ℕ → G → ℝ
  continuous_weight : ∀ n, Continuous (weight n)
  compact_support : ∀ n, HasCompactSupport (weight n)
  nonneg : ∀ n x, 0 ≤ weight n x
  mass : ∀ n, ∫ x, weight n x ∂μ = 1
  control : ∀ Q : Set G, IsCompact Q → ∃ A C : ℝ, 0 ≤ A ∧ 0 ≤ C ∧
    ∀ᶠ n in atTop, ∀ q, q ∈ Q →
      (∀ x, weight n (q⁻¹ * x) - weight n x ≠ 0 → length x ≤ A * scale n) ∧
      (∫ x, |weight n (q⁻¹ * x) - weight n x| ∂μ) ≤ C / scale n

variable (μ : Measure G) [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ρ : G →* (E ≃ₗᵢ[ℝ] E)} {b : G → E}

theorem ControlledReiterFamily.almost_coboundary
    {length : G → ℝ} (F : ControlledReiterFamily μ length)
    (hbc : Continuous b) (hb : IsUnitaryCocycle ρ b)
    (hsub : ∀ δ : ℝ, 0 < δ → ∃ B : ℝ, 0 ≤ B ∧
      ∀ g, ‖b g‖ ≤ δ * length g + B)
    (Q : Set G) (hQ : IsCompact Q) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : E, ∀ q ∈ Q, ‖b q + ρ q φ - φ‖ ≤ ε := by
  obtain ⟨A, C, hA, hC, hcontrol⟩ := F.control Q hQ
  let δ := ε / (2 * (A * C + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨B, hB, hbound⟩ := hsub δ hδ
  have hsmall : δ * A * C ≤ ε / 2 := by
    have he : δ * (2 * (A * C + 1)) = ε :=
      div_mul_cancel₀ _ (by positivity)
    nlinarith
  obtain ⟨n, hn, hcn⟩ := ((F.scale_tendsto.eventually
    (eventually_ge_atTop (2 * B * C / ε))).and hcontrol).exists
  let f := F.weight n
  have hf : Continuous f := F.continuous_weight n
  have hfc : HasCompactSupport f := F.compact_support n
  have hfi : Integrable f μ := hf.integrable_of_hasCompactSupport hfc
  have hfbi : Integrable (fun x => f x • b x) μ :=
    (hf.smul hbc).integrable_of_hasCompactSupport hfc.smul_right
  refine ⟨∫ x, f x • b x ∂μ, fun q hq => ?_⟩
  have hft : Continuous (fun x => f (q⁻¹ * x)) := hf.comp (continuous_const.mul continuous_id)
  have hftc : HasCompactSupport (fun x => f (q⁻¹ * x)) :=
    hfc.comp_homeomorph (Homeomorph.mulLeft q⁻¹)
  have hftbi : Integrable (fun x => f (q⁻¹ * x) • b x) μ :=
    (hft.smul hbc).integrable_of_hasCompactSupport hftc.smul_right
  have hdfi : Integrable (fun x => |f (q⁻¹ * x) - f x|) μ :=
    (hft.sub hf).abs.integrable_of_hasCompactSupport (hftc.sub hfc).abs
  obtain ⟨hsupport, herror⟩ := hcn q hq
  have hlocal (x : G) (hx : f (q⁻¹ * x) - f x ≠ 0) :
      ‖b x‖ ≤ δ * (A * F.scale n) + B :=
    (hbound x).trans (add_le_add
      (mul_le_mul_of_nonneg_left (hsupport x hx) hδ.le) le_rfl)
  have h := hb.norm_haar_weighted_average_le μ f hfi hfbi (F.mass n) q hftbi hdfi hlocal
  have hR := F.scale_pos n
  have hBR : B * C / F.scale n ≤ ε / 2 := by
    apply (div_le_iff₀ hR).2
    have ht := (div_le_iff₀ hε).1 hn
    nlinarith
  calc
    _ ≤ (δ * (A * F.scale n) + B) *
        (∫ x, |f (q⁻¹ * x) - f x| ∂μ) := h
    _ ≤ (δ * (A * F.scale n) + B) * (C / F.scale n) :=
      mul_le_mul_of_nonneg_left herror (by positivity)
    _ = δ * A * C + B * C / F.scale n := by field_simp
    _ ≤ ε := by linarith

end PolycyclicRecognition

end

end OAI
