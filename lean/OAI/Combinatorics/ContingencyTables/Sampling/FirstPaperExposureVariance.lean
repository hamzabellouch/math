import OAI.Combinatorics.ContingencyTables.Transport.ContextChildVariance
import OAI.Combinatorics.ContingencyTables.Transport.RowMajorEnumeration

namespace OAI

/-! # The actual first-paper per-context exposure variance bound -/

namespace ContingencyTables.ExcessContextProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open LargePairEnumeration BalancedFamily BalancedBox IntegerWeightedTransport
open FirstPaperProfiles FirstPaperContextTransport FirstPaperPhysicalMarginal
open PaddedCompletions CompletionCounts

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

lemma later_card_le_allowance (small : I → J → Bool) (s : I×J) {n : ℕ}
    (e : Fin n ≃ Later small s) : n ≤ dimensionAllowance (I := I) (J := J) := by
  have hn : n=Fintype.card (Later small s) := by
    simpa only [Fintype.card_fin] using Fintype.card_congr e
  rw [hn]
  exact (Fintype.card_le_of_injective (fun a : Later small s => a.val) Subtype.val_injective).trans
    ((RowMajorEnumeration.small_card_le_dimension small).trans dimension_le_allowance)

lemma exposure_coefficient (U n d : ℕ) (hd : 1 ≤ d) (hn : n ≤ d) :
    ((U:ℝ)+1)^4*(2+2*n*((U:ℝ)+1)^2) ≤ 4*d*((U:ℝ)+1)^6 := by
  have hn' : (n:ℝ) ≤ d := by exact_mod_cast hn
  have hd' : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hq : (1:ℝ) ≤ ((U:ℝ)+1)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) U]
  have hdq : (1:ℝ) ≤ d*((U:ℝ)+1)^2 := hq.trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hd' (sq_nonneg ((U:ℝ)+1)))
  have hnum : (2:ℝ)+2*n*((U:ℝ)+1)^2 ≤ 4*d*((U:ℝ)+1)^2 := by
    have hh := mul_le_mul_of_nonneg_right hn' (sq_nonneg ((U:ℝ)+1))
    nlinarith
  calc
    _ ≤ ((U:ℝ)+1)^4*(4*d*((U:ℝ)+1)^2) :=
      mul_le_mul_of_nonneg_left hnum (by positivity)
    _ = _ := by ring

/-- The literal source parameters discharge the box, capacity and
signature-side conditions. The only remaining conditions describe the
chosen bounded prefix and a positive-mass exposure context. -/
theorem firstPaper_exposure_variance (r : I → ℕ) (c : J → ℕ)
    (s : I×J) (hs : paperSmall r c s.1 s.2=true) (σ : I×J → ℕ)
    (hσ : ∀ a : Earlier (paperSmall r c) s,
      σ a.val.val ≤ (dimensionAllowance (I := I) (J := J))^20)
    {n : ℕ} (e : Fin n ≃ Later (paperSmall r c) s)
    (H : (Coordinates Bool (widths (fun _ : Fin n => (dimensionAllowance (I := I) (J := J))^20)) → ℕ) → ℝ)
    (hZ : 0 < ∑ j : Fin ((dimensionAllowance (I := I) (J := J))^20+1),
      eliminate (widths (fun _ : Fin n => (dimensionAllowance (I := I) (J := J))^20))
        (contextHard (paperSmall r c)
          (paperCapacity (paperSmall r c) r (dimensionAllowance (I := I) (J := J))
            ((dimensionAllowance (I := I) (J := J))^12) ((dimensionAllowance (I := I) (J := J))^20))
          r c ((dimensionAllowance (I := I) (J := J))^12) _
          (contextEquiv (paperSmall r c) s hs e ((dimensionAllowance (I := I) (J := J))^20))
          (prefixRaw (paperSmall r c) s σ ((dimensionAllowance (I := I) (J := J))^20)))
        (childProfile ((dimensionAllowance (I := I) (J := J))^20) j.val)) :
    let d := dimensionAllowance (I := I) (J := J)
    let U := d^20
    let small := paperSmall r c
    let B := paperCapacity small r d (d^12) U
    let Ms := widths (fun _ : Fin n => U)
    let f := contextHard small B r c (d^12) Ms (contextEquiv small s hs e U) (prefixRaw small s σ U)
    let z := fun j => eliminate Ms f (childProfile U j)
    let μ := fun j => eliminate Ms (fun p => f p*H p) (childProfile U j)/z j
    let E := integerGraphEnergy ((contextVertices U n).filter
      (fun x => InBox (bounds (fun _ : Bool => U) Ms) x ∧ (∑ i, x i)=U+Ms.sum)) f H
    (∑ j : Fin (U+1), z j.val*(μ j.val-
      (∑ k : Fin (U+1),z k.val*μ k.val)/(∑ k : Fin (U+1),z k.val))^2) ≤
      4*d*((U:ℝ)+1)^6*E := by
  dsimp only
  have hd : 2 ≤ dimensionAllowance (I := I) (J := J) := by unfold dimensionAllowance; omega
  have hU : 2 ≤ (dimensionAllowance (I := I) (J := J))^20 :=
    hd.trans (Nat.le_self_pow (by decide) _)
  have hv := physical_child_variance (paperSmall r c)
    (paperCapacity (paperSmall r c) r (dimensionAllowance (I := I) (J := J))
      ((dimensionAllowance (I := I) (J := J))^12) ((dimensionAllowance (I := I) (J := J))^20))
    r c _ s hs σ _ hU
    (fun i j hij => by simp only [paperCapacity,hij,ite_true])
    (fun i j hij => by simp only [paperCapacity,hij,Bool.false_eq_true,ite_false]; omega)
    hσ e (paper_residual_capacity r c _ _ _ dimension_le_allowance) H hZ
  dsimp only at hv
  refine hv.trans (mul_le_mul_of_nonneg_right
    (exposure_coefficient _ n _ (by omega) (later_card_le_allowance _ s e)) ?_)
  exact graphEnergy_nonnegative _ _ _ (contextHard_nonnegative _ _ r c _ _ _ _)

end ContingencyTables.ExcessContextProfiles

end OAI
