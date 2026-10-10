import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperPhysicalMarginal
import OAI.Combinatorics.ContingencyTables.Transport.IntegerContextSlices
import OAI.Combinatorics.ContingencyTables.Transport.IntegerTransportLimit

namespace OAI

/-! # Raw transport for the literal first-paper completion counts

An actual small-coordinate bijection isolates a fixed balanced prefix,
the special pair, and the remaining ordinary pairs. Large completions
are still the original physical finite sum; the prefix coordinates are
excluded from every exchange in the transport graph.
-/

namespace ContingencyTables.FirstPaperContextTransport

open scoped BigOperators Classical Topology
open FirstPaperPhysicalMarginal LargePairEnumeration IntegerWeightedTransport
open BalancedFamily BalancedBox

universe u

variable {I J C : Type u} [Fintype I] [Fintype J] [Fintype C]
  [DecidableEq C]

noncomputable def contextHard (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (Ms : List ℕ)
    (e : (C ⊕ Coordinates Bool Ms) ≃ SmallView (fun a : I×J => small a.1 a.2))
    (σ : C → ℕ) : (Coordinates Bool Ms → ℕ) → ℝ :=
  fun x => hardMarginal small B r c L ((Sum.elim σ x) ∘ e.symm)

noncomputable def contextSoft (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (Ms : List ℕ)
    (e : (C ⊕ Coordinates Bool Ms) ≃ SmallView (fun a : I×J => small a.1 a.2))
    (σ : C → ℕ) (a : ℝ) : (Coordinates Bool Ms → ℕ) → ℝ :=
  fun x => softMarginal small B r c L a ((Sum.elim σ x) ∘ e.symm)

omit [Fintype C] [DecidableEq C] in
theorem contextSoft_nonnegative (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (Ms : List ℕ)
    (e : (C ⊕ Coordinates Bool Ms) ≃ SmallView (fun a : I×J => small a.1 a.2))
    (σ : C → ℕ) (a : ℝ) (x : Coordinates Bool Ms → ℕ) :
    0 ≤ contextSoft small B r c L Ms e σ a x := by
  unfold contextSoft softMarginal
  apply Finset.sum_nonneg
  intro v _
  exact (NestedPenaltyApplication.softWeight_positive _ _ _ _ _ _ _ _).le

/-- The two needed slices are obtained from the physical large-cell
marginal's proved raw signature, then by a principal prefix restriction. -/
theorem contextSoft_slices (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (Ms : List ℕ)
    (e : (C ⊕ Coordinates Bool Ms) ≃ SmallView (fun a : I×J => small a.1 a.2))
    (σ mC : C → ℕ) (m : Bool → ℕ) (R : ℕ)
    (hprefix : InBox mC σ) (a : ℝ) (ha : 0 ≤ a)
    (hlarge : ∀ i j, small i j=false → 2 ≤ B i j) :
    PositiveSlice (contextSoft small B r c L Ms e σ a) (bounds m Ms) (R+Ms.sum) ∧
      RemovalSlice (contextSoft small B r c L Ms e σ a) (bounds m Ms) (R+Ms.sum) := by
  apply context_slices e (softMarginal small B r c L a) mC σ (bounds m Ms)
    (R+Ms.sum) hprefix
  · exact (softMarginal_slices small B r c L a ha _ _ hlarge).1
  · exact (softMarginal_slices small B r c L a ha _ _ hlarge).2

omit [Fintype C] [DecidableEq C] in

theorem contextSoft_tendsto (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (Ms : List ℕ)
    (e : (C ⊕ Coordinates Bool Ms) ≃ SmallView (fun a : I×J => small a.1 a.2))
    (σ : C → ℕ) (x : Coordinates Bool Ms → ℕ) :
    Filter.Tendsto (fun a : ℝ => contextSoft small B r c L Ms e σ a x) Filter.atTop
      (nhds (contextHard small B r c L Ms e σ x)) :=
  softMarginal_tendsto small B r c L _

/-- Hard transport for the actual padded completion count, with the
prefix fixed and only the two endpoint count sums required positive. -/
theorem context_transport (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (Ms : List ℕ)
    (e : (C ⊕ Coordinates Bool Ms) ≃ SmallView (fun a : I×J => small a.1 a.2))
    (σ mC : C → ℕ) (m z : Bool → ℕ) (R W : ℕ)
    (hprefix : InBox mC σ)
    (hlarge : ∀ i j, small i j=false → 2 ≤ B i j)
    (hlower : ∀ U ∈ Ms, 2 ≤ U) (hupper : ∀ U ∈ Ms, U ≤ W)
    (hz : InBox m z) (htotal : (∑ i, z i)=R+1)
    (H : (Coordinates Bool Ms → ℕ) → ℝ)
    (V : Finset (Coordinates Bool Ms → ℕ)) (hV : leafVertices Ms z ⊆ V)
    (hs : 0 < oneHole (eliminate Ms (contextHard small B r c L Ms e σ)) z false)
    (ht : 0 < oneHole (eliminate Ms (contextHard small B r c L Ms e σ)) z true) :
    let f := contextHard small B r c L Ms e σ
    let s := oneHole (eliminate Ms f) z false
    let t := oneHole (eliminate Ms f) z true
    let aux := FactorialSignatures.integerRemovalMatrix (auxiliaryKernel Ms f) z false true
    (oneHole (eliminate Ms (fun p => f p*H p)) z false/s -
      oneHole (eliminate Ms (fun p => f p*H p)) z true/t)^2 ≤
      (1/s+1/t+2*((W:ℝ)+1)^2*aux/(s*t))*integerGraphEnergy V f H := by
  apply integer_root_graph_transport_limit Ms
    (contextSoft small B r c L Ms e σ) _ H
    (contextSoft_tendsto small B r c L Ms e σ) m z R W hlower hupper
    _ hz htotal hs ht V hV
  filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with a ha
  exact ⟨contextSoft_nonnegative small B r c L Ms e σ a,
    contextSoft_slices small B r c L Ms e σ mC m R hprefix a ha hlarge⟩

end ContingencyTables.FirstPaperContextTransport

end OAI
