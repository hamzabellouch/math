import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperContextTransport
import OAI.Combinatorics.ContingencyTables.Transport.IntegerGraphTruncation

namespace OAI

/-! # Literal boxed physical context transport

Auxiliary defect counts use the actual box and total-degree zero extension.
The energy is exactly the bounded physical exchange graph energy. Endpoint
masses and weighted means remain the literal completion-count sums.
-/

namespace ContingencyTables.FirstPaperContextTransport

open scoped BigOperators Classical Topology
open LargePairEnumeration IntegerWeightedTransport BalancedFamily BalancedBox
open IntegerBoxTruncation

universe u

variable {I J C : Type u} [Fintype I] [Fintype J] [Fintype C] [DecidableEq C]

omit [Fintype C] [DecidableEq C] in
lemma contextHard_nonnegative (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (Ms : List ℕ)
    (e : (C ⊕ Coordinates Bool Ms) ≃ SmallView (fun a : I×J => small a.1 a.2))
    (σ : C → ℕ) (x : Coordinates Bool Ms → ℕ) :
    0 ≤ contextHard small B r c L Ms e σ x := by
  apply ge_of_tendsto (contextSoft_tendsto small B r c L Ms e σ x)
  exact Filter.Eventually.of_forall (fun a => contextSoft_nonnegative small B r c L Ms e σ a x)

/-- The physical contextual transport inequality, with every auxiliary
profile and energy endpoint restricted to the declared box and degree. -/
theorem context_box_transport (small : I → J → Bool) (B : I → J → ℕ)
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
    let g := truncate f (bounds m Ms) (R+Ms.sum)
    let s := oneHole (eliminate Ms f) z false
    let t := oneHole (eliminate Ms f) z true
    let aux := FactorialSignatures.integerRemovalMatrix (auxiliaryKernel Ms g) z false true
    (oneHole (eliminate Ms (fun p => f p*H p)) z false/s-
      oneHole (eliminate Ms (fun p => f p*H p)) z true/t)^2 ≤
      (1/s+1/t+2*((W:ℝ)+1)^2*aux/(s*t))*
        integerGraphEnergy (V.filter (fun x => InBox (bounds m Ms) x ∧ (∑ i, x i)=R+Ms.sum)) f H := by
  have h := integer_box_root_transport_limit Ms
    (contextSoft small B r c L Ms e σ) _ H
    (contextSoft_tendsto small B r c L Ms e σ) m z R W hlower hupper
    (by
      filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with a ha
      exact ⟨contextSoft_nonnegative small B r c L Ms e σ a,
        contextSoft_slices small B r c L Ms e σ mC m R hprefix a ha hlarge⟩)
    hz htotal hs ht V hV
  dsimp only at h ⊢
  rw [graphEnergy_truncate V _ H _ _ (contextHard_nonnegative small B r c L Ms e σ)] at h
  exact h

end ContingencyTables.FirstPaperContextTransport

end OAI
