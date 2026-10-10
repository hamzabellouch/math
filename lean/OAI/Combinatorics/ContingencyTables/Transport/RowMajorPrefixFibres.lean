import OAI.Combinatorics.ContingencyTables.Transport.ChoiceContextEnumeration
import OAI.Combinatorics.ContingencyTables.Transport.FinitePrefixVariance
import OAI.Combinatorics.ContingencyTables.Transport.RowMajorEnumeration

namespace OAI

/-! # Row-major word prefixes are the literal physical exposure contexts -/

namespace ContingencyTables.RowMajorEnumeration

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open PhysicalCompletionFibres LargePairEnumeration BalancedFamily
open ExcessContextProfiles SmallGraphProfiles FiniteExposureVariance IntegerWeightedTransport

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable def wordChoices (small : I → J → Bool) (U : ℕ) :
    (Fin (Fintype.card (Cells small)) → Fin (U+1)) ≃ (Cells small → Fin (U+1)) where
  toFun a := a ∘ (enumeration small).symm
  invFun a := a ∘ enumeration small
  left_inv a := by funext i; exact congrArg a ((enumeration small).symm_apply_apply i)
  right_inv a := by funext i; exact congrArg a ((enumeration small).apply_symm_apply i)

noncomputable def earlierWordChoices (small : I → J → Bool) (U : ℕ)
    (k : Fin (Fintype.card (Cells small))) :
    (Fin k.val → Fin (U+1)) ≃ (Earlier small (enumeration small k).val → Fin (U+1)) where
  toFun a := a ∘ (earlierEnumeration small k).symm
  invFun a := a ∘ earlierEnumeration small k
  left_inv a := by funext i; exact congrArg a ((earlierEnumeration small k).symm_apply_apply i)
  right_inv a := by funext i; exact congrArg a ((earlierEnumeration small k).apply_symm_apply i)

lemma earlierEnumeration_cell (small : I → J → Bool) (k : Fin (Fintype.card (Cells small)))
    (j : Fin k.val) :
    (earlierEnumeration small k j).val=enumeration small ⟨j.val,lt_trans j.isLt k.isLt⟩ := rfl

lemma wordChoices_prefix (small : I → J → Bool) (U : ℕ) (k : Fin (Fintype.card (Cells small)))
    (a : Fin (Fintype.card (Cells small)) → Fin (U+1)) :
    earlierChoices small (enumeration small k).val U (wordChoices small U a)=
      earlierWordChoices small U k (restriction k.val (Nat.le_of_lt k.isLt) a) := by
  funext b
  obtain ⟨j,rfl⟩ := (earlierEnumeration small k).surjective b
  change a ((enumeration small).symm (earlierEnumeration small k j).val)=
    restriction k.val (Nat.le_of_lt k.isLt) a ((earlierEnumeration small k).symm (earlierEnumeration small k j))
  rw [earlierEnumeration_cell,Equiv.symm_apply_apply,Equiv.symm_apply_apply]
  rfl

lemma wordChoices_current (small : I → J → Bool) (U : ℕ) (k : Fin (Fintype.card (Cells small)))
    (a : Fin (Fintype.card (Cells small)) → Fin (U+1)) :
    wordChoices small U a (enumeration small k)=a k := by
  exact congrArg a ((enumeration small).symm_apply_apply k)

lemma word_fibre_sum (small : I → J → Bool) (U : ℕ) (k : Fin (Fintype.card (Cells small)))
    (τ : Fin k.val → Fin (U+1)) (j : Fin (U+1)) (F : (Cells small → Fin (U+1)) → ℝ) :
    (∑ a,fibreWeight (fibreWeight (fun a => F (wordChoices small U a))
      (restriction k.val (Nat.le_of_lt k.isLt)) τ) (fun a => a k) j a)=
    ∑ x,fibreWeight (fibreWeight F (earlierChoices small (enumeration small k).val U)
      (earlierWordChoices small U k τ)) (fun x => x (enumeration small k)) j x := by
  apply Fintype.sum_equiv (wordChoices small U)
  intro a
  have hp : earlierChoices small (enumeration small k).val U (wordChoices small U a)=
      earlierWordChoices small U k τ ↔ restriction k.val (Nat.le_of_lt k.isLt) a=τ := by
    rw [wordChoices_prefix]
    exact (earlierWordChoices small U k).apply_eq_iff_eq
  unfold fibreWeight
  dsimp only
  have hc : wordChoices small U a (enumeration small k)=j ↔ a k=j := by
    rw [wordChoices_current]
  by_cases hj : a k=j
  · rw [ite_eq_left hj,ite_eq_left (hc.mpr hj)]
    by_cases hτ : restriction k.val (Nat.le_of_lt k.isLt) a=τ
    · rw [ite_eq_left hτ,ite_eq_left (hp.mpr hτ)]
    · rw [ite_eq_right hτ,ite_eq_right (fun h => hτ (hp.mp h))]
  · rw [ite_eq_right hj,ite_eq_right (fun h => hj (hc.mp h))]

/-- Both zeroth and first moments in the finite prefix variance are
exactly the moments used by the proved physical transport inequality. -/
theorem eliminate_context_eq_word_fibre (small : I → J → Bool) (B : I → J → ℕ)
    (U : ℕ) (hB : ∀ i j,small i j=true → B i j=U)
    (k : Fin (Fintype.card (Cells small))) (τ : Fin k.val → Fin (U+1)) (j : Fin (U+1))
    (F : SmallProfile small → ℝ) :
    let s := (enumeration small k).val
    let hs := (enumeration small k).property
    let σ := prefixExtension small s U (earlierWordChoices small U k τ)
    let e := laterEnumeration small k
    eliminate (widths (fun _ : Fin (Fintype.card (Cells small)-k.val-1) => U))
      (fun p => F (assemble small s hs σ U e p)) (childProfile U j.val)=
      ∑ a,fibreWeight (fibreWeight (fun a => F (rawChoice small U (wordChoices small U a)))
        (restriction k.val (Nat.le_of_lt k.isLt)) τ) (fun a => a k) j a := by
  dsimp only
  rw [eliminate_context_eq_choice_fibre small B _ _ U hB]
  exact (word_fibre_sum small U k τ j (fun x => F (rawChoice small U x))).symm

end ContingencyTables.RowMajorEnumeration

end OAI
