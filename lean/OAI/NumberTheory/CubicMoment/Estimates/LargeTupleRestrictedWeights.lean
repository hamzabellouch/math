import OAI.NumberTheory.CubicMoment.Estimates.LargeTupleWeightLengths

namespace OAI

/-! Actual coordinate weights restricted to either predicate in a fixed
partition of the tuple indices. This preserves the predicate-subtype
indexing in the exact finite convolution identity. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment
variable {i j : ℕ} (P : (Fin i ⊕ Fin j) → Prop) [DecidablePred P]

def largeTupleRestrictedLength (z : largeTupleBoxIndex i j) : ℝ :=
  ∏ a : {a : Fin i ⊕ Fin j // P a}, largeTupleNormScale z.1.2 a

lemma largeTupleRestrictedLength_one (z : largeTupleBoxIndex i j) :
    1 ≤ largeTupleRestrictedLength P z :=
  Finset.one_le_prod₀ (fun a _ => z.property a)

def largeTupleRestrictedWeight (ξ : ℝ) (z : largeTupleBoxIndex i j)
    (a : {a : Fin i ⊕ Fin j // P a}) : ℝ → ℂ :=
  largeTupleCoordinateWeight ξ z.1.1 z.1.2 a

def largeTupleRestrictedLogWeights (ξ : ℝ) :
    LogarithmicWeightFamily
      (fun z : largeTupleBoxIndex i j × {a : Fin i ⊕ Fin j // P a} =>
        largeTupleRestrictedLength P z.1)
      (fun z => largeTupleRestrictedWeight P ξ z.1 z.2) := by
  let hW := (largeTupleCoordinateWeights i j ξ).reindex
    (fun z : largeTupleBoxIndex i j × {a : Fin i ⊕ Fin j // P a} => (z.1.1,z.2.val))
  refine ⟨fun z => largeTupleRestrictedLength_one P z.1,
    hW.compact,hW.positive,hW.smooth,hW.radius,hW.radius_nonneg,hW.support_bound,?_⟩
  intro n
  obtain ⟨C,hC,hbound⟩ := hW.derivative_bound n
  exact ⟨C,0,hC,fun z u => by simpa only [pow_zero,mul_one,largeTupleRestrictedWeight] using hbound z u⟩

lemma largeTupleRestrictedLength_mem (s : Finset (Fin i ⊕ Fin j))
    (z : largeTupleBoxIndex i j) :
    largeTupleRestrictedLength (fun a => a ∈ s) z = largeTupleGroupLength s z := by
  unfold largeTupleRestrictedLength largeTupleGroupLength
  exact (Finset.prod_subtype s (fun _ => Iff.rfl) (fun a => largeTupleNormScale z.1.2 a)).symm

lemma largeTupleRestrictedLength_notMem (s : Finset (Fin i ⊕ Fin j))
    (z : largeTupleBoxIndex i j) :
    largeTupleRestrictedLength (fun a => a ∉ s) z =
      largeTupleGroupLength (Finset.univ\s) z := by
  exact (Finset.prod_subtype (Finset.univ\s) (by simp)
    (fun a => largeTupleNormScale z.1.2 a)).symm

end CubicFirstMoment

end

end OAI
