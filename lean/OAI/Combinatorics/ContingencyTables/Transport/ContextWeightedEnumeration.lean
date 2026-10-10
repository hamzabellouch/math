import OAI.Combinatorics.ContingencyTables.Sampling.SmallContextEnumeration
import OAI.Combinatorics.ContingencyTables.Transport.ExcessContextProfiles

namespace OAI

/-! # Physical observables in the literal conditional enumeration -/

namespace ContingencyTables.SmallContextEnumeration

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres
open LargePairEnumeration BalancedEnumeration BalancedFamily
open FirstPaperContextTransport FirstPaperPhysicalMarginal ExcessContextProfiles
open IntegerWeightedTransport

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

/-- Arbitrary physical observables keep exactly the same completion
multiplicity in recursive elimination and in the literal child fibre. -/
theorem eliminate_context_eq_weighted_sum (small : I → J → Bool) (B : I → J → ℕ)
    (s : I×J) (hs : small s.1 s.2=true) (σ : I×J → ℕ) (U : ℕ)
    (hB : ∀ i j,small i j=true → B i j=U)
    (hσ : ∀ a : Earlier small s,σ a.val.val ≤ U) (k : Fin (U+1))
    {n : ℕ} (e : Fin n ≃ Later small s) (F : SmallProfile small → ℝ) :
    eliminate (widths (fun _ : Fin n => U))
      (fun p => F (assemble small s hs σ U e p)) (childProfile U k.val)=
      ∑ z : BalancedProfiles small B s σ k.val,F (naturalProfile z.val) := by
  rw [eliminate_eq_sum]
  apply Fintype.sum_equiv (((assignmentEquiv (fun _ : Fin n => U)).trans
    (reindexChoices small s e)).trans (balancedContextEquiv small B s hs σ U hB hσ k))
  intro q
  unfold assemble
  rw [physical_embedding_eq small B s hs σ U hB hσ k e q]
  rfl

end ContingencyTables.SmallContextEnumeration

end OAI
