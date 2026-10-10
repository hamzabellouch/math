import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.UniformBallMoments
import OAI.Analysis.RieszRectifiability.Limits.RenormalizedLimitEquation
import OAI.Analysis.RieszRectifiability.Limits.CorrectedRieszLimit

namespace OAI

/-!
# A common height satisfying renormalized equations

The common subsequential height limit inherits the corrected Riesz equations from
uniform local moments and vanishing normalized oscillation. Source-moment tail
control further identifies its renormalized pairing on each admissible ball.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal ENNReal

theorem exists_common_height_with_renormalized_equations {d : ℕ} (p : ℕ)
    (e : (Fin (p + 1) → ℝ) → Ambient d) (π : Ambient d → Fin (p + 1) → ℝ)
    (K Q : ℝ≥0) (he : LipschitzWith K e) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e)
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
        ((σ j).restrict (boundedProjectionRegion π (e 0) K H)))) ≤ E₀ H) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ f : Ambient d → ℝ, Measurable f ∧
      (∀ H, MemLp f 2 ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H))) ∧
      (∀ H, Tendsto (fun j => ∫ x, (u (ρ j) x / δ (ρ j)) ^ 2
        ∂(σ (ρ j)).restrict (boundedProjectionRegion π (e 0) K H)) atTop
        (𝓝 (∫ x, f x ^ 2 ∂(coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)))) ∧
      (∀ H (ψ : Ambient d → ℝ) (L D : ℝ≥0), HasCompactSupport ψ →
        LipschitzWith L ψ → (∀ x, |ψ x| ≤ (D : ℝ)) →
        Tendsto (fun j => ∫ x, (u (ρ j) x / δ (ρ j)) * ψ x
          ∂(σ (ρ j)).restrict (boundedProjectionRegion π (e 0) K H)) atTop
          (𝓝 (∫ x, f x * ψ x
            ∂(coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)))) ∧
      (∀ H, Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) f q.1 q.2)
        (((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)).prod
          ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H))) ∧
        (∫ q : Ambient d × Ambient d, fractionalPairEnergy (p + 1) f q.1 q.2
          ∂(((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)).prod
            ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)))) ≤ E₀ H) ∧
      ∀ (H₀ R : ℝ), 0 ≤ H₀ → 0 < R → 2 * H₀ ≤ R →
        ∀ (B b : ℝ) (N : ℕ → ℕ), G * 2 ^ (p + 1) ≤ B → 0 ≤ b → b < 2 →
          Tendsto N atTop atTop →
          Tendsto (fun j => (R * (2 : ℝ) ^ N j)⁻¹ / δ j) atTop (𝓝 0) →
          (∀ j k, k < N j → (∫ y in dyadicAnnulus (e 0) R k, u j y ^ 2 ∂σ j) ≤
            (B * (R * 2 ^ k) ^ (p + 1)) * (δ j * (R * 2 ^ k) * b ^ k) ^ 2) →
          ∀ (φ η : Ambient d → ℝ) (Lφ Lη Bφ Bη : ℝ≥0),
            LipschitzWith Lφ φ → LipschitzWith Lη η → HasCompactSupport φ → HasCompactSupport η →
            (∀ x, |φ x| ≤ (Bφ : ℝ)) → (∀ x, |η x| ≤ (Bη : ℝ)) →
            (∀ x, φ x ≠ 0 → dist x (e 0) ≤ H₀) →
            (∀ x, η x ≠ 0 → dist x (e 0) ≤ H₀) →
            (∫ x, φ x ∂coordinatePlaneMeasure e) = 0 → (∫ x, η x ∂coordinatePlaneMeasure e) ≠ 0 →
            (Tendsto (fun H => (1 / 2 : ℝ) * (∫ q : Ambient d × Ambient d,
              fractionalBilinear (p + 1) f φ q.1 q.2
                ∂((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)).prod
                  ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H))))
              atTop (𝓝 0)) ∧
            ∀ (J : ℕ) (Bfar : ℝ), 2 * R * ((Q : ℝ) + 1) ≤ J →
              (2 * (Q : ℝ)) ^ (p + 1) * 2 ^ (p + 1) ≤ Bfar →
              (∀ k, ∀ᶠ j in atTop,
                (∫ x in ball (e 0) ((((K : ℝ) + 1) * ((J : ℝ) + 1)) * (2 : ℝ) ^ k),
                  (u j x / δ j) ^ 2 ∂σ j) ≤
                  (Bfar * (R * 2 ^ k) ^ (p + 1)) * ((R * 2 ^ k) * b ^ k) ^ 2) →
              heightPairingOn (p + 1) (coordinatePlaneMeasure e) (e 0) (ball (e 0) R) f φ = 0 := by
  let w := fun j x => u j x / δ j
  obtain ⟨ρ, hρ, f, hfm, hf, hsecond, hmoment, hlim⟩ :=
    exists_global_height_with_local_singular_limits p e π K Q he hπ hleft σ hlocal C G hC hg
      hlower hdiam w (fun j => ((hu j).continuous.div_const (δ j)).measurable)
      hw B₀ E₀ hB₀ henergy hE₀
  refine ⟨ρ, hρ, f, hfm, hf, hsecond, hmoment, fun H => ⟨(hlim H).1, (hlim H).2.1⟩, ?_⟩
  intro H₀ R hH₀ hR hHR B b N hGB hb0 hb2 hN hlast hshell
    φ η Lφ Lη Bφ Bη hφ hη hcφ hcη hBφ hBη hsφ hsη hmean hbump
  let s := boundedProjectionRegion π (e 0) K
  let T := fun H => max R (planeBoxOuterRadius K H) + 1
  have hRT : ∀ H, R ≤ T H := fun H => (le_max_left _ _).trans (le_add_of_nonneg_right (by norm_num))
  have hout : ∀ H, s H ⊆ ball (e 0) (T H) := by
    intro H x hx
    exact hx.2.trans ((le_max_right R (planeBoxOuterRadius K H)).trans_lt (lt_add_one _))
  obtain ⟨M, hM, hnear⟩ := uniform_ball_moments_from_box_moments (p + 1) e π K Q hπ hleft
    σ G hg w hw B₀ hB₀ R hR
  let (H j : ℕ) : IsFiniteMeasure ((σ (ρ j)).restrict (s H)) :=
    boundedProjectionRegion_finite (σ (ρ j)) π (e 0) K H
  have hzero : Tendsto (fun H => (1 / 2 : ℝ) * (∫ q : Ambient d × Ambient d,
      fractionalBilinear (p + 1) f φ q.1 q.2
        ∂((coordinatePlaneMeasure e).restrict (s H)).prod
          ((coordinatePlaneMeasure e).restrict (s H)))) atTop (𝓝 0) := by
    apply corrected_riesz_limiting_equation p G B (fun j => σ (ρ j)) (coordinatePlaneMeasure e)
      (fun ψ => (hlocal ψ).comp hρ.tendsto_atTop) (fun j => hg (ρ j)) hGB (e 0) s
      (fun H => (boundedProjectionRegion_isOpen π hπ.continuous (e 0) K H).measurableSet)
      (eventually_ball_subset_boundedProjectionRegion e π K Q hπ hleft)
      H₀ R hH₀ hR hHR T hRT hout (fun j => u (ρ j)) Ku (fun j => hu (ρ j))
      (fun j => z (ρ j)) (fun j => hz (ρ j)) (fun j => hdiff (ρ j))
      (fun j => δ (ρ j)) (fun j => A (ρ j)) (fun j => v (ρ j)) (fun j => hδ (ρ j))
      (hA.comp hρ.tendsto_atTop) (fun j => hosc (ρ j)) (hratio.comp hρ.tendsto_atTop)
      (fun j => N (ρ j)) (hN.comp hρ.tendsto_atTop) b W hb0 hb2 (fun j => hW (ρ j))
      (hlast.comp hρ.tendsto_atTop) (fun j k hk => hshell (ρ j) k hk)
      M hM (fun j => (hnear (ρ j)).1) (fun j => (hnear (ρ j)).2.1)
      (fun j => (hnear (ρ j)).2.2)
      (fun H j => (hw H (ρ j)).integrable (by norm_num)) (fun H j => henergy H (ρ j))
      f φ η Lφ Lη Bφ Bη hφ hη hcφ hcη hBφ hBη hsφ hsη hmean hbump
    · intro H
      exact (hlim H).2.2 φ Lφ Bφ hφ hBφ
    · intro H
      exact (hlim H).2.2 η Lη Bη hη hBη
  refine ⟨hzero, ?_⟩
  intro J Bfar hJ hBfar hball
  have hνg : GlobalUpperGrowth (p + 1) ((2 * (Q : ℝ)) ^ (p + 1)) (coordinatePlaneMeasure e) := by
    simpa only [Fintype.card_fin] using! coordinatePlaneMeasure_upper_growth e π
      he.continuous.measurable Q hπ hleft
  let := hνg.finite_on_compacts
  have hballL2 : ∀ k j, MemLp (fun x => u (ρ j) x / δ (ρ j)) 2 ((σ (ρ j)).restrict
      (ball (e 0) ((((K : ℝ) + 1) * ((J : ℝ) + 1)) * (2 : ℝ) ^ k))) := by
    intro k j
    obtain ⟨H, hH⟩ := (eventually_ball_subset_boundedProjectionRegion e π K Q hπ hleft
      ((((K : ℝ) + 1) * ((J : ℝ) + 1)) * (2 : ℝ) ^ k)).exists
    exact MemLp.mono_measure (Measure.restrict_mono hH le_rfl) (hw H (ρ j))
  exact renormalized_limit_equation_from_source_moments p e π K Q hπ hleft H₀ R hH₀ hR hHR
    J hJ (fun j => σ (ρ j)) (coordinatePlaneMeasure e) ((2 * (Q : ℝ)) ^ (p + 1)) Bfar
    hνg hBfar (fun j x => u (ρ j) x / δ (ρ j)) f hfm hf hsecond hballL2 b hb0 hb2
    (fun k => hρ.tendsto_atTop.eventually (hball k)) (fun H => (hlim H).1)
    φ Lφ Bφ hφ hcφ hBφ hsφ hmean hzero

end

end RieszRectifiability

end OAI
