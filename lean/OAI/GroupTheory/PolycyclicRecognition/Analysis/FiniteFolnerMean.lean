import OAI.GroupTheory.PolycyclicRecognition.Analysis.FolnerInvariantMean
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! # From finite Følner witnesses to an invariant mean -/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability Filter
open scoped Topology

variable {G : Type*} [Group G] [DecidableEq G]

/-- Finite Følner witnesses, in the symmetric-difference convention used by
the actual finite-average translation estimate. -/
def HasFiniteFolnerSets (G : Type*) [Group G] [DecidableEq G] : Prop :=
  ∀ S : Finset G, ∀ ε : ℝ, 0 < ε →
    ∃ A : Finset G, A.Nonempty ∧ ∀ g ∈ S, boundaryRatio A g < ε

/-- The directed family ranges over every finite set of translations and
every positive reciprocal scale. No countability of the group is required. -/
theorem invariantMean_of_finiteFolnerSets (h : HasFiniteFolnerSets G) :
    Nonempty (InvariantMean G) := by
  have hex (i : Finset G × ℕ) : ∃ A : Finset G, A.Nonempty ∧
      ∀ g ∈ i.1, boundaryRatio A g < 1 / ((i.2 : ℝ) + 1) :=
    h i.1 _ (one_div_pos.mpr (by positivity))
  choose A hA hsmall using hex
  apply exists_invariantMean_of_folner_net (l := atTop) A hA
  intro g
  have hupper : ∀ᶠ i : Finset G × ℕ in atTop,
      boundaryRatio (A i) g ≤ 1 / ((i.2 : ℝ) + 1) := by
    filter_upwards [eventually_ge_atTop (({g} : Finset G), (0 : ℕ))] with i hi
    exact (hsmall i g (Finset.singleton_subset_iff.mp hi.1)).le
  have hsnd : Tendsto (fun i : Finset G × ℕ => i.2) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  have hlim : Tendsto (fun i : Finset G × ℕ => 1 / ((i.2 : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hsnd
  exact squeeze_zero' (Eventually.of_forall (fun i => boundaryRatio_nonneg (A i) g))
    hupper hlim

end PolycyclicRecognition

end

end OAI
