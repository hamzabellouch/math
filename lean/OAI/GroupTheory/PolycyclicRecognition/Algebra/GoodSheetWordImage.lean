import OAI.GroupTheory.PolycyclicRecognition.Analysis.SuccessfulWordPaths
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SupportVisitImage

namespace OAI

/-! # Image bounds for whole words with good intermediate sheets -/

noncomputable section

namespace PolycyclicRecognition

open Set
open scoped NNReal

variable {G W I : Type*} [Group G] [PseudoMetricSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

omit [IsIsometricSMul G G] in
/-- Both support legs have good profiles. Every point of each switch is
near its outgoing endpoint, so no condition on intermediate root sheets
is introduced when concatenating the word. -/
theorem supportWordPath_good_image_bound
    (d f : I → ℝ → G) (hd : ∀ i, Continuous (d i)) (hf : ∀ i, Continuous (f i))
    (hd₀ : ∀ i, d i 0 = 1) (hf₀ : ∀ i, f i 0 = 1) (d₀ : G) (r : ℝ)
    (J : G → W) {K : ℝ≥0} (hJ : LipschitzWith K J)
    (A : Set G) (P : I → ℝ → Prop) (center : W) (E : Set W)
    {L κ B switchError : ℝ} (hL : 0 ≤ L) (hκ : 0 ≤ κ) (hswitchError : 0 ≤ switchError)
    (hbase : ∀ n ∈ A, ∃ w ∈ E, ‖J (n * d₀) - center - r • w‖ ≤ B)
    (hleg : ∀ n ∈ A, ∀ i, ∀ t : unitInterval,
      ∃ w ∈ E, ‖J ((n * d₀) * d i (r * t)) - center - r • w‖ ≤ B)
    (hmetric : ∀ n ∈ A, ∀ i b, P i b → n * f i b ∈ A →
      PathMetricBound (supportVisitPath (d i) (hd i) (hd₀ i)
        (f i) (hf i) (hf₀ i) n d₀ r b) L κ)
    (hswitch : ∀ n ∈ A, ∀ i b, P i b → ∀ t : unitInterval,
      dist (n * f i ((t : ℝ) * b) * (d₀ * d i r)) ((n * d₀) * d i r) ≤ switchError)
    (u : List (I × ℝ)) (hu : ∀ z ∈ u, P z.1 z.2) (n : G)
    (hgood : WordSheetsGood A n (u.map (fun z => f z.1 z.2))) :
    PathMetricBound (supportWordPath d f hd hf hd₀ hf₀ d₀ r u n)
      (L * 2 ^ u.length) (κ * 2 ^ u.length) ∧
      ∀ t, ∃ w ∈ E,
        ‖J (supportWordPath d f hd hf hd₀ hf₀ d₀ r u n t) - center - r • w‖ ≤
          B + K * switchError := by
  apply supportWordPath_good_bound d f hd hf hd₀ hf₀ d₀ r A
    {g | ∃ w ∈ E, ‖J g - center - r • w‖ ≤ B + K * switchError} P hL hκ
  · intro n hn
    obtain ⟨w, hw, hb⟩ := hbase n hn
    exact ⟨w, hw, hb.trans (le_add_of_nonneg_right (mul_nonneg K.coe_nonneg hswitchError))⟩
  · intro n hn i b hb hn'
    refine ⟨hmetric n hn i b hb hn', ?_⟩
    exact supportVisitPath_image_bound (d i) (hd i) (hd₀ i) (f i) (hf i) (hf₀ i)
      J hJ n d₀ r b center E hswitchError (hleg n hn i) (hleg (n * f i b) hn' i)
      (hswitch n hn i b hb)
  · exact hu
  · exact hgood

end PolycyclicRecognition

end

end OAI
