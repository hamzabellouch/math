import OAI.Combinatorics.ProgressionColoring.OuterTestColoring
import OAI.Combinatorics.ProgressionColoring.FairBitProbability

namespace OAI

/-!
# Coloring a finite family of literal supports

The sample space is the actual set of all Boolean assignments to labels. The
events test quarter-balancing on their named supports. Independence is derived
from disjoint supports of the product law, rather than postulated for the tests.
-/

universe uI uLabel

namespace QuantitativeVanDerWaerden

open scoped BigOperators

variable {I : Type uI} {Label : Type uLabel} [Fintype I] [DecidableEq I]
  [Fintype Label] [DecidableEq Label]

/-- Avoidance of tests depends only on the union of their literal supports. -/
theorem outer_avoid_depends {I : Type uI} {Label : Type uLabel} [Fintype I] [DecidableEq I]
    [Fintype Label] [DecidableEq Label]
    (support : I → Finset Label) (T : Finset I) :
    FiniteProbability.DependsOn (T.biUnion support)
      (FiniteLocalLemma.avoid (fun i => fairBalancingBad (support i)) T) := by
  classical
  intro ω η hagree
  simp only [FiniteLocalLemma.mem_avoid]
  have hmem (i : I) (hi : i ∈ T) :
      ω ∈ fairBalancingBad (support i) ↔ η ∈ fairBalancingBad (support i) :=
    fairBalancingBad_depends (support i) ω η
      (fun b hb => hagree b (Finset.mem_biUnion.mpr ⟨i, hi, hb⟩))
  constructor
  · intro h i hi hη
    exact h i hi ((hmem i hi).mpr hη)
  · intro h i hi hω
    exact h i hi ((hmem i hi).mp hω)

theorem outer_nonneighbor_supports_disjoint {I : Type uI} {Label : Type uLabel}
    [Fintype I] [DecidableEq I] [Fintype Label] [DecidableEq Label]
    (support : I → Finset Label)
    (i : I) (T : Finset I) (hiT : i ∉ T)
    (hTN : Disjoint T (outerNeighbors support i)) :
    Disjoint (support i) (T.biUnion support) := by
  classical
  apply Finset.disjoint_left.mpr
  intro b hbi hbT
  obtain ⟨j, hjT, hbj⟩ := Finset.mem_biUnion.mp hbT
  have hjne : j ≠ i := by
    intro h
    subst j
    exact hiT hjT
  have hjN : j ∈ outerNeighbors support i := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ j, hjne, Finset.not_disjoint_iff.mpr ⟨b, hbi, hbj⟩⟩
  exact Finset.disjoint_left.mp hTN hjT hjN

theorem exists_fair_balancing_coloring (support : I → Finset Label)
    (hsize : ∀ i, (100 : ℝ) ≤ (support i).card)
    (hincident : ∀ b,
      ∑ j ∈ Finset.univ.filter (fun j => b ∈ support j),
        Real.exp (-((support j).card : ℝ) / 32) ≤ 1 / 500) :
    ∃ color : Label → Bool, ∀ i b,
      (support i).card ≤ 4 * ((support i).filter fun a => color a = b).card := by
  classical
  let weight : (Label → Bool) → ℝ := FiniteProbability.bernoulliWeight (1 / 2)
  have hw : ∀ ω, 0 ≤ weight ω :=
    FiniteProbability.bernoulliWeight_nonneg (by norm_num) (by norm_num)
  have htotal : ∑ ω, weight ω = 1 := FiniteProbability.sum_bernoulliWeight _
  let P := FiniteLocalLemma.Probability.ofWeights weight hw htotal
  let bad : I → Finset (Label → Bool) := fun i => fairBalancingBad (support i)
  have htail : ∀ i, P.mass (bad i) ≤
      2 * Real.exp (-((support i).card : ℝ) / 8) := by
    intro i
    exact fair_balancing_tail (support i)
  have hindependent : ∀ i T, i ∉ T → Disjoint T (outerNeighbors support i) →
      P.mass (bad i ∩ FiniteLocalLemma.avoid bad T) =
        P.mass (bad i) * P.mass (FiniteLocalLemma.avoid bad T) := by
    intro i T hiT hTN
    exact FiniteProbability.prob_inter_of_disjoint_supports (1 / 2)
      (bad i) (FiniteLocalLemma.avoid bad T) (support i) (T.biUnion support)
      (fairBalancingBad_depends (support i)) (outer_avoid_depends support T)
      (outer_nonneighbor_supports_disjoint support i T hiT hTN)
  obtain ⟨color, hcolor⟩ := outer_exists_avoiding_from_incidence P bad support
    hsize htail hindependent hincident
  refine ⟨color, ?_⟩
  intro i b
  apply Nat.le_of_not_gt
  intro hbad
  exact hcolor i (mem_fairBalancingBad (support i) color |>.mpr ⟨b, hbad⟩)

end QuantitativeVanDerWaerden

end OAI
