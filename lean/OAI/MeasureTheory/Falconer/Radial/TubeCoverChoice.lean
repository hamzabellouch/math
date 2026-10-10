import Mathlib.MeasureTheory.Measure.Prod

namespace OAI

/-! # Measurable choice of countably listed original-label tube covers -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X W ι : Type*} [MeasurableSpace X] [MeasurableSpace W]

theorem tube_cover_uncovered_mass_measurable
    (μ : Measure X) [SFinite μ] (E : Set (X × W)) (hE : MeasurableSet E)
    (U : ι → W → Set X) (hU : ∀ i, MeasurableSet {p : W × X | p.2 ∈ U i p.1})
    (C : Finset ι) :
    Measurable (fun w => μ {x | (x,w) ∈ E ∧ ∀ i ∈ C, x ∉ U i w}) := by
  have hC : MeasurableSet {p : W × X | ∀ i ∈ C, p.2 ∉ U i p.1} := by
    simp only [ofPred_forall]
    exact C.measurableSet_biInter (fun i _ => (hU i).compl)
  exact measurable_measure_prodMk_left ((hE.preimage measurable_swap).inter hC)

theorem exists_measurable_tube_cover_choice
    (μ : Measure X) [SFinite μ] (E : Set (X × W)) (hE : MeasurableSet E)
    (U : ι → W → Set X) (hU : ∀ i, MeasurableSet {p : W × X | p.2 ∈ U i p.1})
    (C : ℕ → Finset ι)
    (hcover : ∀ w, ∃ n, μ {x | (x,w) ∈ E ∧ ∀ i ∈ C n, x ∉ U i w} = 0) :
    ∃ J : W → Finset ι, (∀ i, MeasurableSet {w | i ∈ J w}) ∧
      (∀ w, μ {x | (x,w) ∈ E ∧ ∀ i ∈ J w, x ∉ U i w} = 0) ∧
      ∀ w, ∃ n, J w = C n := by
  classical
  let j : W → ℕ := fun w => Nat.find (hcover w)
  have hj : Measurable j := measurable_find hcover (fun n =>
    measurableSet_eq_fun (tube_cover_uncovered_mass_measurable μ E hE U hU (C n)) measurable_const)
  refine ⟨fun w => C (j w),?_,?_,?_⟩
  · intro i
    exact hj ((Set.to_countable {n | i ∈ C n}).measurableSet)
  · intro w
    exact Nat.find_spec (hcover w)
  · intro w
    exact ⟨j w,rfl⟩

end Falconer

end OAI
