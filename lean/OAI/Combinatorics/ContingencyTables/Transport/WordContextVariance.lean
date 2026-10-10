import OAI.Combinatorics.ContingencyTables.Transport.RowMajorPrefixFibres
import OAI.Combinatorics.ContingencyTables.Sampling.PhysicalContextVariance

namespace OAI

/-! # Physical transport bounds the literal word-prefix child variance -/

namespace ContingencyTables.RowMajorEnumeration

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open PhysicalCompletionFibres LargePairEnumeration BalancedFamily BalancedBox
open ExcessContextProfiles SmallGraphProfiles FiniteExposureVariance IntegerWeightedTransport
open FirstPaperContextTransport FirstPaperPhysicalMarginal PaddedCompletions CompletionCounts

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable def wordWeight (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L U : ℕ)
    (a : Fin (Fintype.card (Cells small)) → Fin (U+1)) : ℝ :=
  hardMarginal small B r c L (rawChoice small U (wordChoices small U a))

noncomputable def wordObservable (small : I → J → Bool) (U : ℕ) (H : SmallProfile small → ℝ)
    (a : Fin (Fintype.card (Cells small)) → Fin (U+1)) : ℝ :=
  H (rawChoice small U (wordChoices small U a))

theorem word_context_variance (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L U : ℕ)
    (hU : 2 ≤ U) (hB : ∀ i j,small i j=true → B i j=U)
    (hlarge : ∀ i j,small i j=false → 2 ≤ B i j)
    (hcap : ∀ T : ResidualTables small r c (fun i => r i+rowLargeCount small i*L)
      (fun j => c j+columnLargeCount small j*L),∀ i j,T.val.val i j ≤ B i j)
    (k : Fin (Fintype.card (Cells small))) (τ : Fin k.val → Fin (U+1))
    (H : SmallProfile small → ℝ) :
    let w := wordWeight small B r c L U
    let G := wordObservable small U H
    let cw := fun j : Fin (U+1) => fibreWeight
      (fibreWeight w (restriction k.val (Nat.le_of_lt k.isLt)) τ) (fun a => a k) j
    let σ := prefixExtension small (enumeration small k).val U (earlierWordChoices small U k τ)
    variance (fun j => ∑ a,cw j a) (fun j => mean (cw j) G) ≤
      ((U:ℝ)+1)^4*(2+2*((Fintype.card (Cells small)-k.val-1:ℕ):ℝ)*((U:ℝ)+1)^2)*
        physicalContextEnergy small B (enumeration small k).val σ (hardMarginal small B r c L) H := by
  dsimp only
  let s := (enumeration small k).val
  let hs := (enumeration small k).property
  let σ := prefixExtension small s U (earlierWordChoices small U k τ)
  let e := laterEnumeration small k
  let Ms := widths (fun _ : Fin (Fintype.card (Cells small)-k.val-1) => U)
  let f := contextHard small B r c L Ms (contextEquiv small s hs e U) (prefixRaw small s σ U)
  let cw := fun j : Fin (U+1) => fibreWeight
    (fibreWeight (wordWeight small B r c L U) (restriction k.val (Nat.le_of_lt k.isLt)) τ) (fun a => a k) j
  have hz (j : Fin (U+1)) : (∑ a,cw j a)=eliminate Ms f (childProfile U j.val) := by
    exact (eliminate_context_eq_word_fibre small B U hB k τ j (hardMarginal small B r c L)).symm
  have hm (j : Fin (U+1)) : (∑ a,cw j a*wordObservable small U H a)=
      eliminate Ms (fun p => f p*H (assemble small s hs σ U e p)) (childProfile U j.val) := by
    have h := eliminate_context_eq_word_fibre small B U hB k τ j
      (fun x => hardMarginal small B r c L x*H x)
    calc
      _ = ∑ a,fibreWeight (fibreWeight
          (fun a => wordWeight small B r c L U a*wordObservable small U H a)
          (restriction k.val (Nat.le_of_lt k.isLt)) τ) (fun a => a k) j a := by
        apply Finset.sum_congr rfl
        intro a _
        exact (double_fibreWeight_mul _ _ _ _ _ _ a).symm
      _ = _ := h.symm
  have hμ (j : Fin (U+1)) : mean (cw j) (wordObservable small U H)=
      eliminate Ms (fun p => f p*H (assemble small s hs σ U e p)) (childProfile U j.val)/
        eliminate Ms f (childProfile U j.val) := by
    unfold mean
    rw [hm,hz]
  change variance (fun j => ∑ a,cw j a) (fun j => mean (cw j) (wordObservable small U H)) ≤ _
  simp_rw [hz,hμ]
  exact physical_context_variance small B r c L s hs σ U hU hB hlarge
    (prefixExtension_bounded small s U (earlierWordChoices small U k τ)) e hcap H

end ContingencyTables.RowMajorEnumeration

end OAI
