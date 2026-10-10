import Mathlib
import OAI.Analysis.RieszRectifiability.Rigidity.AffineHeightRigidity
import OAI.Analysis.RieszRectifiability.Rigidity.DyadicCommonFractionalEquation
import OAI.Analysis.RieszRectifiability.Limits.BoundedAffineStrongLimit

namespace OAI

/-!
# A common affine strong limit from dyadic bounds

The common height limit satisfies a fractional equation whose rigidity forces
it to be affine on the limiting plane. Second-moment and moment convergence then
give strong square-integral convergence to the corresponding ambient affine
height on every bounded projection region, along one shared subsequence.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology SchwartzMap
open scoped NNReal ENNReal ContDiff

theorem exists_common_affine_strong_limit {d : ℕ} (p : ℕ)
    (e : (Fin (p + 1) → ℝ) → Ambient d) (π : Ambient d → Fin (p + 1) → ℝ)
    (K Q : ℝ≥0) (he : LipschitzWith K e) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e)
    (a : Ambient d) (L : Ambient (p + 1) →ₗᵢ[ℝ] Ambient d) (hplane : e = affinePlaneSection a L)
    (σ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (σ j)] [∀ j, SFinite (σ j)]
    (hlocal : CompactTestConvergence σ (coordinatePlaneMeasure e))
    (C G : ℝ) (hC : 0 < C) (hg : ∀ j, GlobalUpperGrowth (p + 1) G (σ j))
    (hlower : ∀ j x, x ∈ (σ j).support → ∀ r : ℝ, AdmissibleRadius (σ j) r →
      ENNReal.ofReal (r ^ (p + 1) / C) ≤ (σ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (σ j).support)
    (u : ℕ → Ambient d → ℝ) (Ku : ℝ≥0) (hu : ∀ j, LipschitzWith Ku (u j))
    (z : ℕ → Ambient d) (hz : ∀ j, ‖z j‖ ≤ 1)
    (hdiff : ∀ j x y, u j x - u j y = inner ℝ (z j) (x - y))
    (δ A v : ℕ → ℝ) (hδ : ∀ j, 0 < δ j) (hA : Tendsto A atTop atTop)
    (hosc : ∀ j, ScalarOscillationBound (p + 1) (σ j) (e 0) (A j) (v j))
    (hratio : Tendsto (fun j => v j / δ j) atTop (𝓝 0))
    (W : ℝ) (hW : ∀ j, |u j (e 0)| ≤ W)
    (hw : ∀ H j, MemLp (fun x => u j x / δ j) 2
      ((σ j).restrict (boundedProjectionRegion π (e 0) K H)))
    (B₀ E₀ : ℕ → ℝ)
    (hB₀ : ∀ H j, (∫ x, (u j x / δ j) ^ 2
      ∂(σ j).restrict (boundedProjectionRegion π (e 0) K H)) ≤ B₀ H)
    (henergy : ∀ H j, Integrable
      (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) (fun x => u j x / δ j) q.1 q.2)
      (((σ j).restrict (boundedProjectionRegion π (e 0) K H)).prod
        ((σ j).restrict (boundedProjectionRegion π (e 0) K H))))
    (hE₀ : ∀ H j, (∫ q : Ambient d × Ambient d,
      fractionalPairEnergy (p + 1) (fun x => u j x / δ j) q.1 q.2
      ∂(((σ j).restrict (boundedProjectionRegion π (e 0) K H)).prod
        ((σ j).restrict (boundedProjectionRegion π (e 0) K H)))) ≤ E₀ H)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (D b : ℝ) (hb0 : 0 ≤ b) (hb2 : b < 2)
    (hlast : Tendsto (fun j => ((2 : ℝ) ^ N j)⁻¹ / δ j) atTop (𝓝 0))
    (hsource : ∀ j l, l ≤ N j → (∫ x in ball (e 0) ((2 : ℝ) ^ l), u j x ^ 2 ∂σ j) ≤
      δ j ^ 2 * D * ((2 : ℝ) ^ l) ^ (p + 1) * ((2 : ℝ) ^ l * b ^ l) ^ 2) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ c : ℝ, ∃ M : Ambient (p + 1) →L[ℝ] ℝ,
      ∀ H, Tendsto (fun j => ∫ x,
        (u (ρ j) x / δ (ρ j) - ambientAffineHeight a L c M x) ^ 2
        ∂(σ (ρ j)).restrict (boundedProjectionRegion π (e 0) K H)) atTop (𝓝 0) := by
  obtain ⟨ρ, hρ, f, hfm, hf, hsecond, hmoment, _, hTail, _, hFractional, T, hT, _⟩ :=
    exists_common_height_with_fractional_equation p e π K Q he hπ hleft a L hplane
      σ hlocal C G hC hg hlower hdiam u Ku hu z hz hdiff δ A v hδ hA hosc hratio W hW
      hw B₀ E₀ hB₀ henergy hE₀ N hN D b hb0 hb2 hlast hsource
  obtain ⟨c, M, hfa⟩ := common_height_intrinsic_ae_affine p e π K Q he hπ hleft a L hplane
    f hf T (fun g => (hT g).2) hFractional (hTail 1 (by norm_num))
  have hsub : CompactTestConvergence (fun j => σ (ρ j)) (coordinatePlaneMeasure e) := by
    intro g
    exact (hlocal g).comp hρ.tendsto_atTop
  refine ⟨ρ, hρ, c, M, ?_⟩
  intro H
  exact bounded_height_strong_of_intrinsic_affine e π K Q he hπ hleft a L hplane
    (fun j => σ (ρ j)) hsub H (fun j x => u (ρ j) x / δ (ρ j))
    (fun j => hw H (ρ j)) f hfm c M hfa (hsecond H) (hmoment H)

end

end RieszRectifiability

end OAI
