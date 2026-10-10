import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.NormalCoordinateTests
import OAI.Analysis.RieszRectifiability.Foundations.SourceNormalizedRegionData

namespace OAI

/-!
# Source energy in a normal frame

Convergence of frame centers gives a common bound for their normal coordinates at
the origin. Applying the scalar source estimates coordinatewise supplies local L²
and fractional pair-energy bounds for normalized normal heights on every fixed ball.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem normalCoordinate_abs_at_zero_le_norm {q d : ℕ} (a : Ambient d)
    (N : Ambient q →ₗᵢ[ℝ] Ambient d) (i : Fin q) :
    |normalCoordinate a N i 0| ≤ ‖a‖ := by
  rw [normalCoordinate_eq_inner]
  simpa only [normalDirection_norm, one_mul, zero_sub, norm_neg] using!
    abs_real_inner_le_norm (normalDirection N i) ((0 : Ambient d) - a)

theorem normalCoordinates_uniform_center_bound {q d : ℕ}
    (a : ℕ → Ambient d) (ha : Tendsto a atTop (𝓝 0))
    (N : ℕ → Ambient q →ₗᵢ[ℝ] Ambient d) :
    ∃ W : ℝ, 0 ≤ W ∧ ∀ j i, |normalCoordinate (a j) (N j) i 0| ≤ W := by
  have hn : Tendsto (fun j => ‖a j‖) atTop (𝓝 0) := by simpa only [norm_zero] using! ha.norm
  have hb : ∀ᶠ j in atTop, ‖a j‖ ≤ 1 :=
    (hn.eventually (gt_mem_nhds zero_lt_one)).mono fun _ h => h.le
  obtain ⟨W, hW, hw⟩ := nonnegative_uniform_bound_of_eventually_le _ 1 hb
  exact ⟨W, hW, fun j i => (normalCoordinate_abs_at_zero_le_norm (a j) (N j) i).trans (hw j)⟩

theorem normal_frame_source_data_on_ball {q d : ℕ} (p : ℕ) (C G : ℝ)
    (μ : ℕ → Measure (Ambient d)) (hg : ∀ j, GlobalUpperGrowth (p + 1) G (μ j))
    (hC : 0 < C)
    (hlower : ∀ j r, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ (p + 1) / C) ≤ (μ j) (ball 0 r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support)
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
    ∀ i : Fin q, ∀ r : ℝ, 0 < r → ∃ B E : ℝ, 0 ≤ B ∧ 0 ≤ E ∧ ∀ j,
      MemLp (fun x => normalCoordinate (a j) (N j) i x / δ j) 2 ((μ j).restrict (ball 0 r)) ∧
      (∫ x in ball 0 r, (normalCoordinate (a j) (N j) i x / δ j) ^ 2 ∂μ j) ≤ B ∧
      Integrable (fun v : Ambient d × Ambient d =>
        fractionalPairEnergy (p + 1) (fun x => normalCoordinate (a j) (N j) i x / δ j) v.1 v.2)
        (((μ j).restrict (ball 0 r)).prod ((μ j).restrict (ball 0 r))) ∧
      (∫ v : Ambient d × Ambient d,
        fractionalPairEnergy (p + 1) (fun x => normalCoordinate (a j) (N j) i x / δ j) v.1 v.2
          ∂((μ j).restrict (ball 0 r)).prod ((μ j).restrict (ball 0 r))) ≤ E := by
  obtain ⟨W, _hW, hw⟩ := normalCoordinates_uniform_center_bound a ha N
  intro i r hr
  obtain ⟨B, hB, hm⟩ := source_normalized_second_moments_on_ball (p + 1) G μ hg
    (fun j => normalCoordinate (a j) (N j) i) 1
    (fun j => normalCoordinate_lipschitz (a j) (N j) i)
    0 δ hδ T hT D b (hsource i) r hr
  obtain ⟨E, hE, he⟩ := source_normalized_energy_on_ball p C G μ hg 0 hC hlower hdiam
    (fun j => normalCoordinate (a j) (N j) i) 1
    (fun j => normalCoordinate_lipschitz (a j) (N j) i)
    (fun j => normalDirection (N j) i) (fun j => (normalDirection_norm (N j) i).le)
    (fun j => normalCoordinate_difference (a j) (N j) i) W (fun j => hw j i)
    δ A hδ hδlim hA hosc T hT D b hb1 hb2 hlast (hsource i) r hr
  exact ⟨B, E, hB, hE, fun j => ⟨(hm j).1, (hm j).2, (he j).1, (he j).2⟩⟩

end

end RieszRectifiability

end OAI
