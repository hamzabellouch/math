import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.ScaledHeightData
import OAI.Analysis.RieszRectifiability.Limits.DyadicCommonAffineStrongLimit

namespace OAI

/-!
# Strong affine limits with positive planar density

Rescaling the measures by the reciprocal limiting density reduces to unit planar
density. Growth, oscillation and local energy estimates scale compatibly, and
canceling the positive scalar transfers the common affine strong limit back.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal ENNReal

theorem exists_common_affine_strong_limit_of_positive_density {d : ℕ} (p : ℕ)
    (e : (Fin (p + 1) → ℝ) → Ambient d) (π : Ambient d → Fin (p + 1) → ℝ)
    (K Q : ℝ≥0) (he : LipschitzWith K e) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e)
    (a : Ambient d) (L : Ambient (p + 1) →ₗᵢ[ℝ] Ambient d) (hplane : e = affinePlaneSection a L)
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)] [∀ j, SFinite (μ j)]
    (ν : Measure (Ambient d)) (hlocal : CompactTestConvergence μ ν)
    (q : ℝ) (hq : 0 < q) (hν : ν = ENNReal.ofReal q • coordinatePlaneMeasure e)
    (C G : ℝ) (hC : 0 < C) (hg : ∀ j, GlobalUpperGrowth (p + 1) G (μ j))
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ (p + 1) / C) ≤ (μ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support)
    (u : ℕ → Ambient d → ℝ) (Ku : ℝ≥0) (hu : ∀ j, LipschitzWith Ku (u j))
    (z : ℕ → Ambient d) (hz : ∀ j, ‖z j‖ ≤ 1)
    (hdiff : ∀ j x y, u j x - u j y = inner ℝ (z j) (x - y))
    (δ A : ℕ → ℝ) (hδ : ∀ j, 0 < δ j) (hδlim : Tendsto δ atTop (𝓝 0))
    (hA : Tendsto A atTop atTop)
    (hosc : ∀ j, ScalarOscillationBound (p + 1) (μ j) (e 0) (A j) (δ j ^ 3))
    (W : ℝ) (hW : ∀ j, |u j (e 0)| ≤ W)
    (hw : ∀ H j, MemLp (fun x => u j x / δ j) 2
      ((μ j).restrict (boundedProjectionRegion π (e 0) K H)))
    (B₀ E₀ : ℕ → ℝ)
    (hB₀ : ∀ H j, (∫ x, (u j x / δ j) ^ 2
      ∂(μ j).restrict (boundedProjectionRegion π (e 0) K H)) ≤ B₀ H)
    (henergy : ∀ H j, Integrable
      (fun v : Ambient d × Ambient d => fractionalPairEnergy (p + 1) (fun x => u j x / δ j) v.1 v.2)
      (((μ j).restrict (boundedProjectionRegion π (e 0) K H)).prod
        ((μ j).restrict (boundedProjectionRegion π (e 0) K H))))
    (hE₀ : ∀ H j, (∫ v : Ambient d × Ambient d,
      fractionalPairEnergy (p + 1) (fun x => u j x / δ j) v.1 v.2
      ∂(((μ j).restrict (boundedProjectionRegion π (e 0) K H)).prod
        ((μ j).restrict (boundedProjectionRegion π (e 0) K H)))) ≤ E₀ H)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (D b : ℝ) (hb0 : 0 ≤ b) (hb2 : b < 2)
    (hlast : Tendsto (fun j => ((2 : ℝ) ^ N j)⁻¹ / δ j) atTop (𝓝 0))
    (hsource : ∀ j l, l ≤ N j → (∫ x in ball (e 0) ((2 : ℝ) ^ l), u j x ^ 2 ∂μ j) ≤
      δ j ^ 2 * D * ((2 : ℝ) ^ l) ^ (p + 1) * ((2 : ℝ) ^ l * b ^ l) ^ 2) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ c : ℝ, ∃ M : Ambient (p + 1) →L[ℝ] ℝ,
      ∀ H, Tendsto (fun j => ∫ x,
        (u (ρ j) x / δ (ρ j) - ambientAffineHeight a L c M x) ^ 2
        ∂(μ (ρ j)).restrict (boundedProjectionRegion π (e 0) K H)) atTop (𝓝 0) := by
  let k : ℝ≥0 := ⟨q⁻¹, (inv_pos.mpr hq).le⟩
  have hk : 0 < k := by exact_mod_cast inv_pos.mpr hq
  have hkR : 0 < (k : ℝ) := NNReal.coe_pos.mpr hk
  have hkq : (k : ℝ) * q = 1 := inv_mul_cancel₀ hq.ne'
  let σ : ℕ → Measure (Ambient d) := fun j => k • μ j
  have hg' : ∀ j, GlobalUpperGrowth (p + 1) ((k : ℝ) * G) (σ j) :=
    fun j => globalUpperGrowth_smul_nnreal (p + 1) G (μ j) (hg j) k
  let (j : ℕ) : IsFiniteMeasureOnCompacts (σ j) := (hg' j).finite_on_compacts
  have hlocal' : CompactTestConvergence σ (coordinatePlaneMeasure e) :=
    compactTestConvergence_cancel_scalar_limit μ ν (coordinatePlaneMeasure e) hlocal q hν k hkq
  have hlower' : ∀ j x, x ∈ (σ j).support → ∀ r : ℝ, AdmissibleRadius (σ j) r →
      ENNReal.ofReal (r ^ (p + 1) / (C / (k : ℝ))) ≤ (σ j) (ball x r) :=
    fun j => lowerGrowth_smul_nnreal (p + 1) C (μ j) hC (hlower j) k hk
  have hdiam' : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (σ j).support := by
    intro r hr
    simpa only [σ, positive_nnreal_smul_support _ k hk] using! hdiam r hr
  have hosc' : ∀ j, ScalarOscillationBound (p + 1) (σ j) (e 0) (A j)
      ((k : ℝ) ^ 2 * δ j ^ 3) :=
    fun j => ScalarOscillationBound.smul_nnreal (p + 1) (μ j) (e 0) (A j) (δ j ^ 3)
      (hosc j) k hk
  have hdata (H j : ℕ) := local_height_data_smul_nnreal (p + 1) (μ j)
    (boundedProjectionRegion π (e 0) K H) (fun x => u j x / δ j) (B₀ H) (E₀ H)
    (hw H j) (hB₀ H j) (henergy H j) (hE₀ H j) k
  obtain ⟨ρ, hρ, c, M, hstrong⟩ := exists_common_affine_strong_limit p e π K Q he hπ hleft
    a L hplane σ hlocal' (C / (k : ℝ)) ((k : ℝ) * G) (div_pos hC hkR) hg' hlower' hdiam'
    u Ku hu z hz hdiff δ A (fun j => (k : ℝ) ^ 2 * δ j ^ 3) hδ hA hosc'
    (scaled_cubic_oscillation_ratio_tendsto δ hδ hδlim k) W hW
    (fun H j => (hdata H j).1) (fun H => (k : ℝ) * B₀ H) (fun H => (k : ℝ) ^ 2 * E₀ H)
    (fun H j => (hdata H j).2.1) (fun H j => (hdata H j).2.2.1)
    (fun H j => (hdata H j).2.2.2) N hN ((k : ℝ) * D) b hb0 hb2 hlast
    (dyadic_source_moments_smul_nnreal (p + 1) μ (e 0) u δ N D b hsource k)
  refine ⟨ρ, hρ, c, M, fun H => ?_⟩
  exact tendsto_setIntegral_of_positive_nnreal_smul (fun j => μ (ρ j))
    (boundedProjectionRegion π (e 0) K H)
    (fun j x => (u (ρ j) x / δ (ρ j) - ambientAffineHeight a L c M x) ^ 2)
    k hk (hstrong H)

end

end RieszRectifiability

end OAI
