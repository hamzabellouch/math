import OAI.Combinatorics.ContingencyTables.Sampling.SmallContextEnumeration

namespace OAI

/-! # Actual exposure child masses retain all physical completions -/

namespace ContingencyTables.SmallContextEnumeration

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres PaddedCompletions CompletionCounts
open FirstPaperProfiles FirstPaperPhysicalMarginal FirstPaperContextTransport
open LargePairEnumeration BalancedFamily IntegerWeightedTransport

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

theorem eliminate_context_eq_child_card (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    (s : I×J) (hs : small s.1 s.2=true) (σ : I×J → ℕ) (U : ℕ)
    (hB : ∀ i j, small i j=true → B i j=U)
    (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U) (k : Fin (U+1))
    {n : ℕ} (e : Fin n ≃ Later small s)
    (hcap : ∀ T : ResidualTables small r c
      (fun i => r i+rowLargeCount small i*L) (fun j => c j+columnLargeCount small j*L),
      ∀ i j, T.val.val i j ≤ B i j) :
    eliminate (widths (fun _ : Fin n => U))
      (contextHard small B r c L _ (contextEquiv small s hs e U) (prefixRaw small s σ U))
      (childProfile U k.val)=
      (Fintype.card (SmallResidualChild small (r) (fun i => r i+rowLargeCount small i*L)
        c (fun j => c j+columnLargeCount small j*L) s σ k.val):ℝ) := by
  rw [eliminate_context_eq_balanced_mass small B r c L s hs σ U hB hσ k e]
  exact balanced_mass_eq_child_card small B r c L s σ k.val hs hcap

/-- In the paper's actual parameters, no extra capacity hypothesis is
needed for the literal conditional completion count. -/
theorem firstPaper_child_mass (r : I → ℕ) (c : J → ℕ)
    (s : I×J) (hs : paperSmall r c s.1 s.2=true) (σ : I×J → ℕ)
    (hσ : ∀ a : Earlier (paperSmall r c) s,
      σ a.val.val ≤ (dimensionAllowance (I := I) (J := J))^20)
    (k : Fin ((dimensionAllowance (I := I) (J := J))^20+1))
    {n : ℕ} (e : Fin n ≃ Later (paperSmall r c) s) :
    let d := dimensionAllowance (I := I) (J := J)
    let small := paperSmall r c
    let B := paperCapacity small r d (d^12) (d^20)
    eliminate (widths (fun _ : Fin n => d^20))
      (contextHard small B r c (d^12) _ (contextEquiv small s hs e (d^20))
        (prefixRaw small s σ (d^20))) (childProfile (d^20) k.val)=
      (Fintype.card (SmallResidualChild small r (fun i => r i+rowLargeCount small i*d^12)
        c (fun j => c j+columnLargeCount small j*d^12) s σ k.val):ℝ) := by
  dsimp only
  exact eliminate_context_eq_child_card _ _ r c _ s hs σ _
    (fun i j hij => by simp only [paperCapacity,hij,ite_true]) hσ k e
    (paper_residual_capacity r c _ _ _ dimension_le_allowance)

end ContingencyTables.SmallContextEnumeration

end OAI
