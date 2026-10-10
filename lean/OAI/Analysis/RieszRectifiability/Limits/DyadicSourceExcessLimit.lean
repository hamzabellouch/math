import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.DyadicNormalAffineLimit
import OAI.Analysis.RieszRectifiability.Flatness.NormalAffineExcessBridge

namespace OAI

/-!
# Vanishing normalized excess along dyadic source limits

The common affine limits of normal coordinates determine improved approximating planes.
Dyadic source moments provide uniform local second-moment bounds, allowing the normal-frame
excess estimate to show that squared excess divided by the original scale squared tends to zero
along one subsequence at every nonnegative radius.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal ENNReal

theorem exists_dyadic_source_excess_limit {p d : ℕ}
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (C G : ℝ) (hC : 0 < C) (hg : ∀ j, GlobalUpperGrowth (p + 1) G (μ j))
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ (p + 1) / C) ≤ (μ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support)
    (hzero : ∀ j, (0 : Ambient d) ∈ (μ j).support)
    (S : ℕ → AffineSubspace ℝ (Ambient d)) (hS : ∀ j, IsAffineNPlane (p + 1) (S j))
    (δ : ℕ → ℝ) (T : ℕ → ℕ) (hδ : Tendsto δ atTop (𝓝 0)) (hT : Tendsto T atTop atTop)
    (M b : ℝ)
    (hmoment : ∀ j l, l ≤ T j →
      (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l), infDist x (S j : Set (Ambient d)) ^ 2 ∂μ j) ≤
        M * (δ j * b ^ l) ^ 2 * ((2 : ℝ) ^ l) ^ (p + 1 + 2))
    (A : ℕ → ℝ) (hA : Tendsto A atTop atTop)
    (hosc : ∀ j, ScalarOscillationBound (p + 1) (μ j) 0 (A j) (δ j ^ 3))
    (D : ℝ≥0)
    (hB : ∀ j ε, 0 < ε → ∀ u : Ambient d → ℝ, MemLp u 2 (μ j) →
      MemLp (truncated (p + 1) (μ j) ε u) 2 (μ j) ∧
        eLpNorm (truncated (p + 1) (μ j) ε u) 2 (μ j) ≤ (D : ℝ≥0∞) * eLpNorm u 2 (μ j))
    (hδpos : ∀ j, 0 < δ j) (hb1 : 1 ≤ b) (hb2 : b < 2)
    (hlast : Tendsto (fun j => ((2 : ℝ) ^ T j)⁻¹ / δ j) atTop (𝓝 0)) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∀ r : ℝ, 0 ≤ r →
      Tendsto (fun j => squaredExcess (p + 1) (μ (ρ j)) 0 r / δ (ρ j) ^ 2) atTop (𝓝 0) := by
  classical
  obtain ⟨ρ, hρ, _, _, _, a, L, N, Llim, _, _, _, _, _, _, _, _, horth, hsplit, hdist,
    c, B, hstrong⟩ := exists_dyadic_normal_affine_limit μ C G hC hg hlower hdiam hzero
      S hS δ T hδ hT M b hmoment A hA hosc D hB hδpos hb1 hb2 hlast
  let K : ℝ≥0 := ((Fintype.card (Fin (p + 1)) : ℝ≥0) ^ (1 / (2 : ℝ≥0∞)).toReal)
  let π := affinePlaneCoordinates (0 : Ambient d) Llim
  have he0 : affinePlaneSection (0 : Ambient d) Llim 0 = 0 := by simp [affinePlaneSection]
  have hsource (i : Fin (d - (p + 1))) (j l : ℕ) (hl : l ≤ T (ρ j)) :
      (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l), normalCoordinate (a j) (N j) i x ^ 2 ∂μ (ρ j)) ≤
        δ (ρ j) ^ 2 * M * ((2 : ℝ) ^ l) ^ (p + 1) * ((2 : ℝ) ^ l * b ^ l) ^ 2 :=
    normalCoordinate_dyadic_source_bound (μ (ρ j)) G (hg (ρ j))
      (S (ρ j)) (hS (ρ j)).1 (a j) (N j) (hdist j) M (δ (ρ j)) b l (hmoment (ρ j) l hl) i
  have hdata : ∀ i : Fin (d - (p + 1)), ∀ H : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ j,
      MemLp (fun x => normalCoordinate (a j) (N j) i x / δ (ρ j)) 2
        ((μ (ρ j)).restrict (boundedProjectionRegion π 0 K H)) ∧
      (∫ x in boundedProjectionRegion π 0 K H,
        (normalCoordinate (a j) (N j) i x / δ (ρ j)) ^ 2 ∂μ (ρ j)) ≤ B := by
    intro i H
    obtain ⟨B, hB, hb⟩ := source_normalized_second_moments_on_ball (p + 1) G (fun j => μ (ρ j))
      (fun j => hg (ρ j)) (fun j => normalCoordinate (a j) (N j) i) 1
      (fun j => normalCoordinate_lipschitz (a j) (N j) i) 0 (fun j => δ (ρ j))
      (fun j => hδpos (ρ j)) (fun j => T (ρ j)) (hT.comp hρ.tendsto_atTop)
      M b (hsource i) (planeBoxOuterRadius K H) (planeBoxOuterRadius_pos K H)
    refine ⟨B, hB, fun j => ?_⟩
    have hs : boundedProjectionRegion π 0 K H ⊆ ball 0 (planeBoxOuterRadius K H) := inter_subset_right
    have hμ := Measure.restrict_mono (μ := μ (ρ j)) hs le_rfl
    exact ⟨MemLp.mono_measure hμ (hb j).1,
      (integral_mono_measure hμ
        (Eventually.of_forall fun x => sq_nonneg (normalCoordinate (a j) (N j) i x / δ (ρ j)))
        (hb j).1.integrable_sq).trans (hb j).2⟩
  choose B₀ hB₀ hdata₀ using hdata
  let Bound : ℕ → ℝ := fun H => ∑ i, B₀ i H
  have hbound (i : Fin (d - (p + 1))) (H : ℕ) : B₀ i H ≤ Bound H :=
    Finset.single_le_sum (fun j _ => hB₀ j H) (Finset.mem_univ i)
  have hlim := normal_frame_excess_of_common_affine_coordinates
    (affinePlaneSection 0 Llim) π K ‖Llim.toContinuousLinearMap.adjoint‖₊
    (affinePlaneCoordinates_lipschitz 0 Llim) (affinePlaneCoordinates_leftInverse 0 Llim)
    0 Llim (fun j => μ (ρ j)) a L N horth hsplit (fun j => δ (ρ j))
    (fun j => hδpos (ρ j)) (hδ.comp hρ.tendsto_atTop)
    (fun i H j => by simpa only [he0] using! (hdata₀ i H j).1) Bound
    (fun i H j => by simpa only [he0] using! ((hdata₀ i H j).2.trans (hbound i H)))
    c B (by simpa only [he0] using! hstrong)
  exact ⟨ρ, hρ, by simpa only [he0] using! hlim⟩

end

end RieszRectifiability

end OAI
