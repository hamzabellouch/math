import Mathlib
import OAI.Analysis.RieszRectifiability.Packing.DyadicFittingFrameLimit

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem plane_moment_tendsto_zero_from_dyadic {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (S : ℕ → AffineSubspace ℝ (Ambient d)) (hS : ∀ j, (S j : Set (Ambient d)).Nonempty)
    (hdyadic : ∀ l : ℕ, Tendsto (fun j => ∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l),
      infDist x (S j : Set (Ambient d)) ^ 2 ∂μ j) atTop (𝓝 0)) (R : ℝ) :
    Tendsto (fun j => ∫ x in ball (0 : Ambient d) R,
      infDist x (S j : Set (Ambient d)) ^ 2 ∂μ j) atTop (𝓝 0) := by
  obtain ⟨l, _hl, hlarge⟩ := exists_nat_pow_near (le_max_left (1 : ℝ) R) (by norm_num : (1 : ℝ) < 2)
  have hsub : ball (0 : Ambient d) R ⊆ ball 0 ((2 : ℝ) ^ (l + 1)) :=
    ball_subset_ball ((le_max_right 1 R).trans hlarge.le)
  apply squeeze_zero (fun j => integral_nonneg (fun x => sq_nonneg (infDist x (S j : Set (Ambient d)))))
    _ (hdyadic (l + 1))
  intro j
  exact setIntegral_mono_set
    (squared_infDist_integrableOn_ball (μ j) 0 ((2 : ℝ) ^ (l + 1)) _ (hS j))
    (Eventually.of_forall (fun x => sq_nonneg (infDist x (S j : Set (Ambient d)))))
    (Eventually.of_forall (fun _ hx => hsub hx))

theorem fixed_plane_moment_tendsto_zero_on_ball {n d : ℕ}
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (S : ℕ → AffineSubspace ℝ (Ambient d)) (hS : ∀ j, (S j : Set (Ambient d)).Nonempty)
    (δ : ℕ → ℝ) (T : ℕ → ℕ) (hδ : Tendsto δ atTop (𝓝 0)) (hT : Tendsto T atTop atTop)
    (M b : ℝ)
    (hmoment : ∀ j l, l ≤ T j →
      (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l), infDist x (S j : Set (Ambient d)) ^ 2 ∂μ j) ≤
        M * (δ j * b ^ l) ^ 2 * ((2 : ℝ) ^ l) ^ (n + 2)) (R : ℝ) :
    Tendsto (fun j => ∫ x in ball (0 : Ambient d) R,
      infDist x (S j : Set (Ambient d)) ^ 2 ∂μ j) atTop (𝓝 0) :=
  plane_moment_tendsto_zero_from_dyadic μ S hS
    (fixed_plane_dyadic_moment_tendsto_zero μ S δ T hδ hT M b hmoment) R

end

end RieszRectifiability

end OAI
