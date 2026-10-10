import OAI.NumberTheory.DukePrimeDegree.Entropy.FirstReturnPartition

namespace OAI

/-! # Entropy of measurable finite refinements on the return levels -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace DukePrimeDegree

theorem firstReturn_cells_information_summable
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ) (hE : MeasurableEmbedding T)
    {S : Set Y} (hS : MeasurableSet S)
    (K : ℕ → ℕ) (B : ∀ n, Y → Fin (K n)) (hB : ∀ n, Measurable (B n))
    (C : ℝ) (hcard : ∀ n, Real.log (K n) ≤ C*(n+1)) :
    Summable (fun z : Σ n : ℕ, Fin (K n) =>
      Real.negMulLog (μ.real {x | x ∈ firstReturnLevel T S z.1 ∧ B z.1 x=z.2})) := by
  let p := fun n (i : Fin (K n)) =>
    μ.real {x | x ∈ firstReturnLevel T S n ∧ B n x=i}
  have hmass (n : ℕ) : ∑ i, p n i=μ.real (firstReturnLevel T S n) := by
    have hd : Pairwise (fun i j : Fin (K n) => Disjoint
        {x | x ∈ firstReturnLevel T S n ∧ B n x=i}
        {x | x ∈ firstReturnLevel T S n ∧ B n x=j}) := by
      intro i j hij
      exact Set.disjoint_left.mpr (fun x hi hj => hij (hi.2.symm.trans hj.2))
    have hm (i : Fin (K n)) : MeasurableSet
        {x | x ∈ firstReturnLevel T S n ∧ B n x=i} :=
      (measurableSet_firstReturnLevel hT.measurable hS n).inter (hB n (measurableSet_singleton i))
    change (∑ i, μ.real {x | x ∈ firstReturnLevel T S n ∧ B n x=i})=_
    rw [←measureReal_iUnion_fintype hd hm]
    congr 1
    ext x
    simp only [mem_iUnion,mem_ofPred_eq]
    exact ⟨fun ⟨_,hx,_⟩ => hx,fun hx => ⟨B n x,hx,rfl⟩⟩
  exact refined_return_information_summable K p
    (fun n => μ.real (firstReturnLevel T S n))
    (fun _ _ => measureReal_nonneg) hmass (fun _ => measureReal_le_one)
    (summable_firstReturnLevel_mass μ hT hE hS) C hcard

end DukePrimeDegree

end

end OAI
