import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.SeparatedParameterPatchGluing
import OAI.Analysis.RieszRectifiability.Surfaces.RescaledBallCharts

namespace OAI

namespace RieszRectifiability

noncomputable section

open Metric Set
open scoped NNReal

theorem exists_ball_lipschitz_cover_of_rescaled_children {n d : ℕ} {ι : Type*}
    (a : ι → Ambient n) (c : ι → Ambient d) (r : ι → ℝ)
    (f : ∀ i : ι, ball (0 : Ambient n) (r i) → Ambient d)
    (M A L : ℝ≥0) (hA : 0 < A)
    (hsep : ∀ i j : ι, i ≠ j → r i + r j ≤ (A : ℝ) * dist (a i) (a j))
    (hcenters : ∀ i j : ι, dist (c i) (c j) ≤ (L : ℝ) * dist (a i) (a j))
    (himage : ∀ i : ι, Set.range (f i) ⊆ closedBall (c i) (3 * r i))
    (hLip : ∀ i : ι, LipschitzWith M (f i))
    (ρ : ℝ) (hball : ∀ i : ι, ball (a i) (r i / (4 * (A : ℝ))) ⊆ ball (0 : Ambient n) ρ) :
    ∃ F : ball (0 : Ambient n) ρ → Ambient d,
      LipschitzWith (lipschitzExtensionConstant (Ambient d) *
        separatedPatchGluingConstant (M * (4 * A)) A L) F ∧
      (⋃ i : ι, Set.range (f i)) ⊆ Set.range F := by
  classical
  have hs : 0 < 4 * A := by positivity
  have hc (i : ι) := exists_rescaled_ball_chart (r i) (a i) (4 * A) hs (f i) M (hLip i)
  choose g hg hrange using hc
  have hrange' (i : ι) : g i '' ball (a i) (r i / (4 * (A : ℝ))) = Set.range (f i) := by
    simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using! hrange i
  have hg' (i : ι) : LipschitzOnWith (M * (4 * A)) (g i)
      (ball (a i) (r i / (4 * (A : ℝ)))) := by
    simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using! hg i
  obtain ⟨F, hF, hcover⟩ := exists_ball_lipschitz_cover_of_separated_parameter_patches
    a c r (fun i => ball (a i) (r i / (4 * (A : ℝ)))) g (M * (4 * A)) A L hA hsep hcenters
    (fun _ _ hu => le_of_lt hu)
    (fun i u hu => himage i (hrange' i ▸ mem_image_of_mem (g i) hu)) hg'
    ρ (iUnion_subset hball)
  refine ⟨F, hF, ?_⟩
  intro y hy
  obtain ⟨i, hi⟩ := mem_iUnion.mp hy
  exact hcover (mem_iUnion.mpr ⟨i, hrange' i ▸ hi⟩)

theorem small_parameter_ball_subset_double_ball {n : ℕ}
    (a : Ambient n) (ρ r : ℝ) (hρ : 0 < ρ) (ha : a ∈ closedBall (0 : Ambient n) ρ)
    (s : ℝ≥0) (hs : 1 ≤ s) (hr : r ≤ ρ) :
    ball a (r / (s : ℝ)) ⊆ ball (0 : Ambient n) (2 * ρ) := by
  intro u hu
  have hs' : 1 ≤ (s : ℝ) := hs
  have hsp : 0 < (s : ℝ) := lt_of_lt_of_le zero_lt_one hs'
  have hrad : r / (s : ℝ) ≤ ρ := (div_le_iff₀ hsp).mpr (by nlinarith)
  have hnear : dist u a < r / (s : ℝ) := hu
  have hac : dist a (0 : Ambient n) ≤ ρ := ha
  have ht := dist_triangle u a (0 : Ambient n)
  change dist u (0 : Ambient n) < 2 * ρ
  linarith

end

end RieszRectifiability

end OAI
