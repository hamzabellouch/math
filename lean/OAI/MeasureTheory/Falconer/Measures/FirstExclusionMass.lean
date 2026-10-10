import OAI.MeasureTheory.Falconer.Estimates.SphericalEnergy

namespace OAI

/-! # Charging each pair only at its first exclusion scale -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X]

def firstExclusion (E : ℕ → Set X) (n : ℕ) : Set X :=
  E n \ ⋃ j ∈ Finset.range n, E j

theorem measurableSet_firstExclusion (E : ℕ → Set X)
    (hE : ∀ n, MeasurableSet (E n)) (n : ℕ) : MeasurableSet (firstExclusion E n) :=
  (hE n).diff (Finset.measurableSet_biUnion _ (fun j _ => hE j))

omit [MeasurableSpace X] in
theorem union_exclusion_subset_initial_first (E : ℕ → Set X) (K : ℕ) :
    (⋃ n, E n) ⊆ (⋃ j ∈ Finset.range K, E j) ∪ ⋃ n, firstExclusion E (K+n) := by
  classical
  intro x hx
  have hex : ∃ n, x ∈ E n := mem_iUnion.mp hx
  let N := Nat.find hex
  have hN : x ∈ E N := Nat.find_spec hex
  by_cases hNK : N < K
  · exact Or.inl (mem_iUnion₂.mpr ⟨N,Finset.mem_range.mpr hNK,hN⟩)
  · have hKN : K ≤ N := Nat.le_of_not_gt hNK
    apply Or.inr
    apply mem_iUnion.mpr
    refine ⟨N-K,?_⟩
    rw [Nat.add_sub_of_le hKN]
    refine ⟨hN,?_⟩
    intro hprev
    obtain ⟨j,hj,hxj⟩ := mem_iUnion₂.mp hprev
    exact Nat.find_min hex (Finset.mem_range.mp hj) hxj

theorem union_exclusion_mass (μ : Measure X) (E : ℕ → Set X) (K : ℕ)
    {A : ℝ≥0∞} (cost : ℕ → ℝ≥0∞)
    (hinit : μ (⋃ j ∈ Finset.range K, E j) ≤ A)
    (hlate : ∀ n, μ (firstExclusion E (K+n)) ≤ cost n) :
    μ (⋃ n, E n) ≤ A+∑' n, cost n := by
  apply (measure_mono (union_exclusion_subset_initial_first E K)).trans
  apply (measure_union_le _ _).trans
  exact add_le_add hinit ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum hlate))

end Falconer

end OAI
