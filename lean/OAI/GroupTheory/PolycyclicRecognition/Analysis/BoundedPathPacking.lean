import OAI.GroupTheory.PolycyclicRecognition.Analysis.BoundedPathGrowth
import OAI.GroupTheory.PolycyclicRecognition.Analysis.MeasurePacking

namespace OAI

/-!
# From polynomial-volume thickenings to bounded-height path packing

The endpoint set need not be measurable. We pack finite separated subsets using
Haar mass and then take a maximal one. Only the enclosing coordinate regions
are measured; this is the precise bridge needed from the Lie-coordinate bounds.
-/

namespace PolycyclicRecognition

open MeasureTheory MeasureTheory.Measure Metric
open scoped ENNReal

variable {G W : Type*} [Group G] [MetricSpace G] [MeasurableSpace G]
  [BorelSpace G] [MeasurableMul G] [IsIsometricSMul G G] [NormedAddCommGroup W]

/-- Endpoints of at most `n` bounded-height steps from a fixed starting point. -/
def boundedChainEndpoints (π : G → W) (L M : ℝ) (n : ℕ) (x : G) : Set G :=
  {y | ∃ m ≤ n, BoundedHeightChain π L M m x y}

/-- A polynomial-volume region containing the half-unit thickening of the
bounded-chain endpoints gives the required polynomial covering bound. -/
theorem boundedChain_cover_of_volume
    (μ : Measure G) [IsMulLeftInvariant μ] (π : G → W)
    (x : G) (L M : ℝ) (C b : ℕ) (region : ℕ → Set G)
    (hq0 : μ (ball (1 : G) (1 / 2)) ≠ 0)
    (hqtop : μ (ball (1 : G) (1 / 2)) ≠ ⊤)
    (hthick : ∀ n y, y ∈ boundedChainEndpoints π L M n x →
      ball y (1 / 2) ⊆ region n)
    (hvol : ∀ n, μ (region n) ≤
      ((C * (1 + n) ^ b : ℕ) : ℝ≥0∞) * μ (ball (1 : G) (1 / 2))) :
    ∃ centers : ℕ → Finset G,
      (∀ n, (centers n).card ≤ C * (1 + n) ^ b) ∧
      ∀ n m, m ≤ n → ∀ y, BoundedHeightChain π L M m x y →
        ∃ c ∈ centers n, dist y c ≤ 1 := by
  classical
  have hn (n : ℕ) := finite_cover_set_of_separated_bound
    (boundedChainEndpoints π L M n x) (r := 1) (by norm_num) (C * (1 + n) ^ b)
    (fun t ht hs => separated_card_le_polynomial μ t (1 / 2) (region n) C b n hq0 hqtop
      (by intro a ha d hd had; have := hs a ha d hd had; linarith)
      (fun y hy => hthick n y (ht hy)) (hvol n))
  choose centers _ hcard hcover using hn
  exact ⟨centers, hcard, fun n m hm y hy => hcover n y ⟨m, hm, hy⟩⟩

end PolycyclicRecognition

end OAI
