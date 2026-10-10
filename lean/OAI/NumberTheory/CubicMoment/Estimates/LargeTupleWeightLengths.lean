import OAI.NumberTheory.CubicMoment.Estimates.LargeTupleCoordinateWeights
import OAI.NumberTheory.CubicMoment.Estimates.LogarithmicWeightFamily

namespace OAI

/-! The same actual coordinate weights are logarithmic families when
the length is the product of any fixed group of their scales. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def largeTupleBoxIndex (i j : ℕ) :=
  {z : {X : ℝ // 0 < X} × ((Fin i ⊕ Fin j) → ℕ) //
    ∀ a, 1 ≤ largeTupleNormScale z.2 a}

def largeTupleGroupLength {i j : ℕ} (s : Finset (Fin i ⊕ Fin j))
    (z : largeTupleBoxIndex i j) : ℝ := ∏ a ∈ s, largeTupleNormScale z.1.2 a

lemma largeTupleGroupLength_one {i j : ℕ} (s : Finset (Fin i ⊕ Fin j))
    (z : largeTupleBoxIndex i j) : 1 ≤ largeTupleGroupLength s z :=
  Finset.one_le_prod₀ (fun a _ => z.property a)

def largeTupleGroupWeight {i j : ℕ} (ξ : ℝ) (s : Finset (Fin i ⊕ Fin j))
    (z : largeTupleBoxIndex i j) (a : s) : ℝ → ℂ :=
  largeTupleCoordinateWeight ξ z.1.1 z.1.2 a

def largeTupleGroupWeights {i j : ℕ} (ξ : ℝ) (s : Finset (Fin i ⊕ Fin j)) :
    UniformLogWeights (fun z : largeTupleBoxIndex i j × s => largeTupleGroupWeight ξ s z.1 z.2) :=
  (largeTupleCoordinateWeights i j ξ).reindex (fun z : largeTupleBoxIndex i j × s => (z.1.1,z.2.val))

def largeTupleGroupLogWeights {i j : ℕ} (ξ : ℝ) (s : Finset (Fin i ⊕ Fin j)) :
    LogarithmicWeightFamily
      (fun z : largeTupleBoxIndex i j × s => largeTupleGroupLength s z.1)
      (fun z => largeTupleGroupWeight ξ s z.1 z.2) := by
  let hW := largeTupleGroupWeights ξ s
  refine ⟨fun z => largeTupleGroupLength_one s z.1,hW.compact,hW.positive,hW.smooth,
    hW.radius,hW.radius_nonneg,hW.support_bound,?_⟩
  intro n
  obtain ⟨C,hC,hbound⟩ := hW.derivative_bound n
  exact ⟨C,0,hC,fun z u => by simpa only [pow_zero,mul_one] using hbound z u⟩

end CubicFirstMoment

end

end OAI
