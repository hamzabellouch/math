import OAI.GroupTheory.PolycyclicRecognition.Analysis.RightFolnerExpansion
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! # One source Følner sequence works for every metric radius -/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability Filter Metric
open scoped Topology

variable {G : Type*} [Group G] [MetricSpace G] [IsIsometricSMul G G] [DecidableEq G]

theorem finiteMetricNeighborhood_mono
    (hfinite : ∀ R : ℝ, (closedBall (1 : G) R).Finite)
    (E : Finset G) {R S : ℝ} (hRS : R ≤ S) :
    finiteMetricNeighborhood hfinite E R ⊆ finiteMetricNeighborhood hfinite E S := by
  intro x hx
  obtain ⟨p, hp, hd⟩ := (mem_finiteMetricNeighborhood hfinite E R x).mp hx
  exact (mem_finiteMetricNeighborhood hfinite E S x).mpr ⟨p, hp, hd.trans hRS⟩

theorem exists_sourceMetricFolner_sequence (M : InvariantMean G)
    (hfinite : ∀ R : ℝ, (closedBall (1 : G) R).Finite) :
    ∃ E : ℕ → Finset G, (∀ n, (E n).Nonempty) ∧
      ∀ R : ℝ, Tendsto
        (fun n => ((finiteMetricNeighborhood hfinite (E n) R \ E n).card : ℝ) / (E n).card)
        atTop (𝓝 0) := by
  have hex (n : ℕ) : ∃ E : Finset G, E.Nonempty ∧
      ((finiteMetricNeighborhood hfinite E n \ E).card : ℝ) <
        (1 / ((n : ℝ) + 1)) * E.card :=
    exists_small_metricNeighborhood M hfinite n (by positivity)
  choose E hE hsmall using hex
  refine ⟨E, hE, fun R => ?_⟩
  obtain ⟨N, hN⟩ := exists_nat_ge R
  have hupper : ∀ᶠ n : ℕ in atTop,
      ((finiteMetricNeighborhood hfinite (E n) R \ E n).card : ℝ) / (E n).card ≤
        1 / ((n : ℝ) + 1) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    have hRn : R ≤ (n : ℝ) := hN.trans (by exact_mod_cast hn)
    have hc : (finiteMetricNeighborhood hfinite (E n) R \ E n).card ≤
        (finiteMetricNeighborhood hfinite (E n) n \ E n).card :=
      Finset.card_le_card (by
        intro x hx
        obtain ⟨hx, hxE⟩ := Finset.mem_sdiff.mp hx
        exact Finset.mem_sdiff.mpr
          ⟨finiteMetricNeighborhood_mono hfinite (E n) hRn hx, hxE⟩)
    apply (div_le_iff₀ (by exact_mod_cast (hE n).card_pos)).mpr
    have hcr : ((finiteMetricNeighborhood hfinite (E n) R \ E n).card : ℝ) ≤
        (finiteMetricNeighborhood hfinite (E n) n \ E n).card := by exact_mod_cast hc
    exact hcr.trans (hsmall n).le
  exact squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) hupper
    tendsto_one_div_add_atTop_nhds_zero_nat

end PolycyclicRecognition

end

end OAI
