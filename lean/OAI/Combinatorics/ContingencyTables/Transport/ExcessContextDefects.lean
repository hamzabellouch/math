import OAI.Combinatorics.ContingencyTables.Transport.ExcessContextProfiles

namespace OAI

/-! # Auxiliary raw profiles satisfy the literal physical defect equation -/

namespace ContingencyTables.ExcessContextProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open PhysicalCompletionFibres LargePairEnumeration BalancedFamily BalancedBox
open BalancedEnumeration IntegerWeightedTransport FirstPaperProfiles

universe u

variable {I J : Type u} [LinearOrder I] [LinearOrder J]

lemma defect_of_pair_totals (small : I → J → Bool) (B : I → J → ℕ) (U : ℕ)
    (hU : 1 ≤ U) (hB : ∀ i j, small i j=true → B i j=U)
    (s t : I×J) (hs : small s.1 s.2=true) (ht : small t.1 t.2=true) (hst : s≠t)
    (z : SmallProfile small) (hz : ∀ a, z a ≤ U)
    (hpair : ∀ a : Cells small, z (a,false)+z (a,true)=
      if a.val=s then U-1 else if a.val=t then U+1 else U) :
    IsDefect (smallView small z false) (smallQ small B z) s t := by
  refine ⟨hst,?_⟩
  intro i j
  cases hij : small i j
  · have hns : ¬(i=s.1 ∧ j=s.2) := by
      rintro ⟨rfl,rfl⟩
      rw [hs] at hij
      contradiction
    have hnt : ¬(i=t.1 ∧ j=t.2) := by
      rintro ⟨rfl,rfl⟩
      rw [ht] at hij
      contradiction
    simp only [transferInt,smallView,smallQ,hij,Bool.false_eq_true,↓reduceDIte,
      hns,hnt,↓reduceIte]
    norm_num
  · have hp := hpair ⟨(i,j),hij⟩
    have hx := hz (⟨(i,j),hij⟩,false)
    have hy := hz (⟨(i,j),hij⟩,true)
    dsimp only at hp
    by_cases his : i=s.1 ∧ j=s.2
    · have his' : (i,j)=s := Prod.ext his.1 his.2
      have hit : ¬(i=t.1 ∧ j=t.2) := by
        intro hit
        exact hst (his'.symm.trans (Prod.ext hit.1 hit.2))
      rw [ite_eq_left his'] at hp
      simp only [transferInt,smallView,smallQ,hij,dite_eq_left,hB i j hij,
        ite_eq_left his,ite_eq_right hit]
      omega
    · have his' : (i,j)≠s := fun h => his (Prod.ext_iff.mp h)
      rw [ite_eq_right his'] at hp
      by_cases hit : i=t.1 ∧ j=t.2
      · have hit' : (i,j)=t := Prod.ext hit.1 hit.2
        rw [ite_eq_left hit'] at hp
        simp only [transferInt,smallView,smallQ,hij,dite_eq_left,hB i j hij,
          ite_eq_right his,ite_eq_left hit]
        omega
      · have hit' : (i,j)≠t := fun h => hit (Prod.ext_iff.mp h)
        rw [ite_eq_right hit'] at hp
        simp only [transferInt,smallView,smallQ,hij,dite_eq_left,hB i j hij,
          ite_eq_right his,ite_eq_right hit]
        omega

noncomputable def boundedExcess (small : I → J → Bool) (B : I → J → ℕ)
    (s : I×J) (hs : small s.1 s.2=true) (σ : I×J → ℕ) (U l : ℕ)
    (hl : l ≤ U) (hB : ∀ i j, small i j=true → B i j=U)
    (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U) {n : ℕ} (e : Fin n ≃ Later small s)
    (q : ExcessAssignments (widths (fun _ : Fin n => U)))
    (hq : ValidExcess _ q) : BoundedProfile small B := fun a =>
  ⟨rawExcess small s hs σ U l e q a,by
    rw [hB _ _ a.1.property]
    exact Nat.lt_succ_of_le (rawExcess_bounded small s hs σ U l hl hσ e q hq a)⟩

lemma naturalProfile_boundedExcess (small : I → J → Bool) (B : I → J → ℕ)
    (s : I×J) (hs : small s.1 s.2=true) (σ : I×J → ℕ) (U l : ℕ)
    (hl : l ≤ U) (hB : ∀ i j, small i j=true → B i j=U)
    (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U) {n : ℕ} (e : Fin n ≃ Later small s)
    (q : ExcessAssignments (widths (fun _ : Fin n => U))) (hq : ValidExcess _ q) :
    naturalProfile (boundedExcess small B s hs σ U l hl hB hσ e q hq)=
      rawExcess small s hs σ U l e q := rfl

noncomputable def excessDefectProfile (small : I → J → Bool) (B : I → J → ℕ)
    (s : I×J) (hs : small s.1 s.2=true) (σ : I×J → ℕ) (U l : ℕ)
    (hl0 : 1 ≤ l) (hlU : l ≤ U) (hB : ∀ i j, small i j=true → B i j=U)
    (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U) {n : ℕ} (e : Fin n ≃ Later small s)
    (q : ExcessAssignments (widths (fun _ : Fin n => U))) (hq : ValidExcess _ q) :
    DefectProfiles small B s (e (excessIndex (fun _ : Fin n => U) q)).val.val σ l := by
  let t := e (excessIndex (fun _ : Fin n => U) q)
  refine ⟨boundedExcess small B s hs σ U l hlU hB hσ e q hq,?_,?_,?_⟩
  · rw [naturalProfile_boundedExcess]
    apply defect_of_pair_totals small B U (by omega) hB s t.val.val hs t.val.property
      t.property.ne (rawExcess small s hs σ U l e q)
      (rawExcess_bounded small s hs σ U l hlU hσ e q hq)
    intro a
    have hh := rawExcess_pair_total small s hs σ U l hl0 hlU hσ e q a
    simpa only [Subtype.ext_iff] using hh
  · intro i j hij hbefore
    simp only [naturalProfile_boundedExcess,smallView,hij,dite_eq_left]
    have hh := assemble_prefix small s hs σ U e
      (excessEmbedding _ (auxRoot U l) q) ⟨⟨(i,j),hij⟩,hbefore⟩ false
    exact hh
  · simp only [naturalProfile_boundedExcess,smallView,hs,dite_eq_left,rawExcess,
      assemble_special,excessEmbedding_root,auxRoot,Bool.false_eq_true,↓reduceIte]

end ContingencyTables.ExcessContextProfiles

end OAI
