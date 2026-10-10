import OAI.Analysis.CoulombTransport.LocalBranchMeasure
import OAI.Analysis.CoulombTransport.SplittingConstruction

namespace OAI

universe uAlpha uIndex

/-!
# The local-homeomorphism selection obstruction

The local branch maps need not be measurable away from their source. Extending
them by a constant, then using concentration of the reference measure, gives
the exact obstruction stated for the original maps and their pushforwards.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace Problem356.LocalSplitting

open LocalBranchMeasure Splitting

variable {α : Type uAlpha} {ι : Type uIndex} [TopologicalSpace α] [MeasurableSpace α]
  [BorelSpace α] [MeasurableEq α] [Fintype ι]

/-- Local homeomorphic branches on disjoint components cannot admit a
measure-preserving deterministic selector when the central weight is larger. -/
theorem no_preserving_local_branch_selection
    (z : α) (e : ι → OpenPartialHomeomorph α α)
    {ν : Measure α} [IsFiniteMeasure ν] {B : Set α} {c d : ℝ≥0∞}
    (hν : ν univ ≠ 0) (hB : MeasurableSet B)
    (hfull : ∀ᵐ x ∂ν, x ∈ B)
    (hSource : ∀ i, B ⊆ (e i).source)
    (hCentral : ∀ i, Disjoint B (e i '' B))
    (hPair : Pairwise fun i j => Disjoint (e i '' B) (e j '' B))
    (hdc : d < c) :
    ¬ ∃ T : α → α, Measurable T ∧
      Measure.map T (splitMeasure ν c (fun _ => d) (fun i => e i)) =
        splitMeasure ν c (fun _ => d) (fun i => e i) ∧
      (∀ᵐ x ∂ν, ∃ i, T x = e i x) := by
  let H : ι → α → α := fun i => extendedBranch (e i) z
  have hImage : ∀ i S, S ⊆ B → H i '' S = e i '' S := by
    intro i S hS
    exact extendedBranch_image (e i) z (hS.trans (hSource i))
  have hMap : ∀ i, Measure.map (H i) ν = Measure.map (e i) ν := by
    intro i
    apply map_extendedBranch (e i) z ν
    exact hfull.mono fun x hx => hSource i hx
  have hMixture : splitMeasure ν c (fun _ => d) H =
      splitMeasure ν c (fun _ => d) (fun i => e i) := by
    unfold splitMeasure
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [hMap i]
  have hNo := no_preserving_splitMeasure_selection (H := H) hν hB hfull
    (fun i => measurable_extendedBranch (e i) z)
    (fun i => injOn_extendedBranch (e i) z (hSource i))
    (fun i S hS hSB => measurableSet_extendedBranch_image (e i) z hS
      (hSB.trans (hSource i)))
    (fun i => by rw [hImage i B subset_rfl]; exact hCentral i)
    (fun i j hij => by
      change Disjoint (H i '' B) (H j '' B)
      rw [hImage i B subset_rfl, hImage j B subset_rfl]
      exact hPair hij) hdc
  rintro ⟨T, hT, hPres, hSel⟩
  apply hNo
  refine ⟨T, hT, ?_, ?_⟩
  · simpa only [hMixture] using hPres
  · filter_upwards [hfull, hSel] with x hx hxSel
    obtain ⟨i, hi⟩ := hxSel
    refine ⟨i, ?_⟩
    exact hi.trans (extendedBranch_apply_of_mem (e i) z (hSource i hx)).symm

/-- The coefficients and four branches used by the Coulomb counterexample. -/
theorem no_preserving_four_local_branches
    (z : α) (e : Fin 4 → OpenPartialHomeomorph α α)
    {ν : Measure α} [IsProbabilityMeasure ν] {B : Set α}
    (hB : MeasurableSet B) (hfull : ∀ᵐ x ∂ν, x ∈ B)
    (hSource : ∀ i, B ⊆ (e i).source)
    (hCentral : ∀ i, Disjoint B (e i '' B))
    (hPair : Pairwise fun i j => Disjoint (e i '' B) (e j '' B)) :
    ¬ ∃ T : α → α, Measurable T ∧
      Measure.map T (splitMeasure ν (1 / 3) (fun _ => 1 / 6) (fun i => e i)) =
        splitMeasure ν (1 / 3) (fun _ => 1 / 6) (fun i => e i) ∧
      (∀ᵐ x ∂ν, ∃ i, T x = e i x) := by
  apply no_preserving_local_branch_selection z e (by simp) hB hfull hSource hCentral hPair
  norm_num

end Problem356.LocalSplitting

end

end OAI
