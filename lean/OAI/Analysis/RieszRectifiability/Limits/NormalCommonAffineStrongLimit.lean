import Mathlib
import OAI.Analysis.RieszRectifiability.Packing.NormalFrameSourceEnergy
import OAI.Analysis.RieszRectifiability.Limits.ScaledCommonAffineStrongLimit
import OAI.Analysis.RieszRectifiability.Limits.FiniteCommonSubsequence

namespace OAI

/-!
# Simultaneous affine limits of normal coordinates

Uniform source-energy bounds and a positive planar weak limit yield local strong convergence
of each normalized normal coordinate to an affine height. Stability under further extraction
allows a finite common subsequence to realize all normal-coordinate limits on every bounded
projection region at once.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal ENNReal

theorem exists_normal_common_affine_strong_limit {p q d : ℕ}
    (e : (Fin (p + 1) → ℝ) → Ambient d) (π : Ambient d → Fin (p + 1) → ℝ)
    (K Q : ℝ≥0) (he : LipschitzWith K e) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e)
    (L : Ambient (p + 1) →ₗᵢ[ℝ] Ambient d) (hplane : e = affinePlaneSection 0 L)
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (ν : Measure (Ambient d)) (hlocal : CompactTestConvergence μ ν)
    (t : ℝ) (ht : 0 < t) (hν : ν = ENNReal.ofReal t • coordinatePlaneMeasure e)
    (C G : ℝ) (hC : 0 < C) (hg : ∀ j, GlobalUpperGrowth (p + 1) G (μ j))
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ (p + 1) / C) ≤ (μ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support)
    (hzero : ∀ j, (0 : Ambient d) ∈ (μ j).support)
    (a : ℕ → Ambient d) (ha : Tendsto a atTop (𝓝 0))
    (N : ℕ → Ambient q →ₗᵢ[ℝ] Ambient d)
    (δ A : ℕ → ℝ) (hδ : ∀ j, 0 < δ j) (hδlim : Tendsto δ atTop (𝓝 0))
    (hA : Tendsto A atTop atTop)
    (hosc : ∀ j, ScalarOscillationBound (p + 1) (μ j) 0 (A j) (δ j ^ 3))
    (T : ℕ → ℕ) (hT : Tendsto T atTop atTop) (D b : ℝ) (hb1 : 1 ≤ b) (hb2 : b < 2)
    (hlast : Tendsto (fun j => ((2 : ℝ) ^ T j)⁻¹ / δ j) atTop (𝓝 0))
    (hsource : ∀ i j l, l ≤ T j →
      (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l), normalCoordinate (a j) (N j) i x ^ 2 ∂μ j) ≤
        δ j ^ 2 * D * ((2 : ℝ) ^ l) ^ (p + 1) * ((2 : ℝ) ^ l * b ^ l) ^ 2) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ c : Fin q → ℝ,
      ∃ M : Fin q → Ambient (p + 1) →L[ℝ] ℝ, ∀ i H,
        Tendsto (fun j => ∫ x,
          (normalCoordinate (a (ρ j)) (N (ρ j)) i x / δ (ρ j) -
            ambientAffineHeight 0 L (c i) (M i) x) ^ 2
          ∂(μ (ρ j)).restrict (boundedProjectionRegion π 0 K H)) atTop (𝓝 0) := by
  classical
  have he0 : e 0 = 0 := by simp [hplane, affinePlaneSection]
  obtain ⟨W, _, hW⟩ := normalCoordinates_uniform_center_bound a ha N
  have hball := normal_frame_source_data_on_ball p C G μ hg hC
    (fun j r hr => hlower j 0 (hzero j) r hr) hdiam a ha N
    δ A hδ hδlim hA hosc T hT D b hb1 hb2 hlast hsource
  let P : Fin q → (ℕ → ℕ) → Prop := fun i ρ =>
    ∃ c : ℝ, ∃ M : Ambient (p + 1) →L[ℝ] ℝ, ∀ H,
      Tendsto (fun j => ∫ x,
        (normalCoordinate (a (ρ j)) (N (ρ j)) i x / δ (ρ j) - ambientAffineHeight 0 L c M x) ^ 2
        ∂(μ (ρ j)).restrict (boundedProjectionRegion π 0 K H)) atTop (𝓝 0)
  have hextract : ∀ i ρ, StrictMono ρ → ∃ σ : ℕ → ℕ, StrictMono σ ∧ P i (ρ ∘ σ) := by
    intro i ρ hρ
    obtain ⟨B, E, hdata⟩ := normalized_region_data_of_ball_data (p + 1) μ
      (fun j x => normalCoordinate (a j) (N j) i x / δ j) 0 (hball i) π K
    have hdata' (H j : ℕ) := (hdata H).2.2 (ρ j)
    have hlocal' : CompactTestConvergence (fun j => μ (ρ j)) ν :=
      fun g => (hlocal g).comp hρ.tendsto_atTop
    obtain ⟨σ, hσ, c, M, hs⟩ := exists_common_affine_strong_limit_of_positive_density p e π K Q
      he hπ hleft 0 L hplane (fun j => μ (ρ j)) ν hlocal' t ht hν C G hC
      (fun j => hg (ρ j)) (fun j => hlower (ρ j))
      (fun r hr => hρ.tendsto_atTop.eventually (hdiam r hr))
      (fun j => normalCoordinate (a (ρ j)) (N (ρ j)) i) 1
      (fun j => normalCoordinate_lipschitz (a (ρ j)) (N (ρ j)) i)
      (fun j => normalDirection (N (ρ j)) i)
      (fun j => (normalDirection_norm (N (ρ j)) i).le)
      (fun j => normalCoordinate_difference (a (ρ j)) (N (ρ j)) i)
      (fun j => δ (ρ j)) (fun j => A (ρ j)) (fun j => hδ (ρ j))
      (hδlim.comp hρ.tendsto_atTop) (hA.comp hρ.tendsto_atTop)
      (fun j => by simpa only [he0] using! hosc (ρ j)) W
      (fun j => by simpa only [he0] using! hW (ρ j) i)
      (fun H j => by simpa only [he0] using! (hdata' H j).1) B E
      (fun H j => by simpa only [he0] using! (hdata' H j).2.1)
      (fun H j => by simpa only [he0] using! (hdata' H j).2.2.1)
      (fun H j => by simpa only [he0] using! (hdata' H j).2.2.2)
      (fun j => T (ρ j)) (hT.comp hρ.tendsto_atTop) D b (zero_le_one.trans hb1) hb2
      (hlast.comp hρ.tendsto_atTop)
      (fun j l hl => by simpa only [he0] using! hsource i (ρ j) l hl)
    refine ⟨σ, hσ, c, M, ?_⟩
    simpa only [he0, Function.comp_apply] using! hs
  have hstable : ∀ i ρ σ, P i ρ → StrictMono σ → P i (ρ ∘ σ) := by
    intro i ρ σ hP hσ
    obtain ⟨c, M, hs⟩ := hP
    exact ⟨c, M, fun H => (hs H).comp hσ.tendsto_atTop⟩
  obtain ⟨ρ, hρ, hs⟩ := exists_finite_common_subsequence P hextract hstable
  choose c M hM using hs
  exact ⟨ρ, hρ, c, M, hM⟩

end

end RieszRectifiability

end OAI
