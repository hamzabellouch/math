import OAI.Analysis.KadisonKastler.RegularCoreCommutant
import OAI.Analysis.KadisonKastler.AbelianActionStability

namespace OAI

/-! # The regular core gap from the tensor gap

The fixed-point comparison uses the actual invariant mean for the additive
real group. It does not assert that an ordinary gap survives tensor
amplification: the tensor gap remains explicit in this theorem.
-/

namespace KadisonKastler

open MeasureTheory
open scoped Topology

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

/-- For one common regular action, passage from the tensor algebras to
their actual generated cores decreases the gap. -/
theorem kkDistance_regularCore_le_tensor
    (hComm : PublishedRegularCommutant.{u})
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hU : ∀ ξ, Continuous (fun t : ℝ =>
      (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ))
    (M N : VonNeumannAlgebra H)
    (hM : ∀ s T, T ∈ M → unitaryConj (U s) T ∈ M)
    (hN : ∀ s T, T ∈ N → unitaryConj (U s) T ∈ N) :
    kkDistance (regularCoreAlgebra U hU M) (regularCoreAlgebra U hU N) ≤
      kkDistance (regularTensorAlgebra M) (regularTensorAlgebra N) := by
  rw [regularCoreAlgebra_eq_fixed_of_published hComm U hU M hM,
    regularCoreAlgebra_eq_fixed_of_published hComm U hU N hN]
  let : TopologicalSpace (Multiplicative ℝ) := ⊥
  let : DiscreteTopology (Multiplicative ℝ) := ⟨rfl⟩
  exact kkDistance_abelian_fixedPointAlgebra_le (regularCoreAction U)
    (regularTensorAlgebra M) (regularTensorAlgebra N)
    (regularCoreAction_normalizes_tensor U M hM)
    (regularCoreAction_normalizes_tensor U N hN)

end

end KadisonKastler

end OAI
