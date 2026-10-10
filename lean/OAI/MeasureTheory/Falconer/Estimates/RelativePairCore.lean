import OAI.MeasureTheory.Falconer.Measures.PairCorePruning
import OAI.MeasureTheory.Falconer.Estimates.SourceClassOriginalLaws
import OAI.MeasureTheory.Falconer.Radial.OccupiedRadialTree
import OAI.MeasureTheory.Falconer.Recursion.ProfileBalls

namespace OAI

/-! # Discarding null source and pin sets relative to the incoming relation -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem relative_pair_core_null (μ : Measure X) (ν : Measure Y) [SFinite ν]
    (G : Set (X × Y)) (A : Set X) (P : Set Y) (hA : μ Aᶜ = 0) (hP : ν Pᶜ = 0) :
    (μ.prod ν) (G \ (G ∩ (A ×ˢ P))) = 0 := by
  apply le_antisymm _ zero_le
  apply (measure_mono (show G \ (G ∩ (A ×ˢ P)) ⊆ (A ×ˢ P)ᶜ from ?_)).trans_eq
    (product_core_compl_null μ ν A P hA hP)
  intro x hx hcore
  exact hx.2 ⟨hx.1,hcore⟩

theorem relative_pruning_cost_trans {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (G H K : Set X) {a b : ℝ≥0∞} (hGH : μ (G \ H) ≤ a) (hHK : μ (H \ K) ≤ b) :
    μ (G \ K) ≤ a+b := by
  have hsub : G \ K ⊆ (G \ H) ∪ (H \ K) := by
    intro x hx
    by_cases hh : x ∈ H
    · exact Or.inr ⟨hh,hx.2⟩
    · exact Or.inl ⟨hx.1,hh⟩
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add hGH hHK))

namespace Regularization
variable {d : ℕ}

theorem source_class_pair_core (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ ν : Measure (Space d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (N B : ℕ) (p : CellPath d) (hp : p ∈ regularizationLeaves Q μ N)
    (A P : Set (Space d)) (hA : MeasurableSet A) (hP : MeasurableSet P)
    (hAfull : μ Aᶜ = 0) (hPfull : ν Pᶜ = 0)
    (G : Set (Space d × Space d)) (hG : MeasurableSet G) :
    ∃ G₀ : Set (Space d × Space d), MeasurableSet G₀ ∧ G₀ ⊆ G ∧
      G₀ ⊆ (A ∩ Q.occupiedTreeCore (sourceClass Q μ N B p) N) ×ˢ P ∧
      ((sourceClass Q μ N B p).prod ν) (G \ G₀) = 0 := by
  let ρ := sourceClass Q μ N B p
  have : IsProbabilityMeasure ρ := regularization_class_probability Q hQ μ N B hp
  let S := A ∩ Q.occupiedTreeCore ρ N
  have hS : MeasurableSet S := hA.inter (Q.occupiedTreeCore_measurable ρ N)
  have hSfull : ρ Sᶜ = 0 := by
    rw [show Sᶜ = Aᶜ ∪ (Q.occupiedTreeCore ρ N)ᶜ by exact compl_inter _ _]
    apply le_antisymm _ zero_le
    apply (measure_union_le _ _).trans_eq
    rw [sourceClass_absolutelyContinuous Q μ N B p hAfull,
      Q.occupiedTreeCore_full ρ N (sourceClass_root_null Q hQ μ N B p),add_zero]
  refine ⟨G ∩ (S ×ˢ P),hG.inter (hS.prod hP),inter_subset_left,inter_subset_right,?_⟩
  exact relative_pair_core_null ρ ν G S P hSfull hPfull

end Regularization
end Falconer

end OAI
