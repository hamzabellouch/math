import OAI.Combinatorics.ContingencyTables.Sampling.SmallGraphProfiles
import OAI.Combinatorics.ContingencyTables.Transport.ContextChildVariance

namespace OAI

/-! # Context leaf vertices are actual balanced or single-defect states -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open PhysicalCompletionFibres LargePairEnumeration BalancedFamily BalancedBox
open BalancedEnumeration IntegerWeightedTransport FirstPaperProfiles ExcessContextProfiles FactorialSignatures

universe u

lemma pair_total_removeOne {C : Type*} [DecidableEq C]
    (D : C×Bool → ℕ) (c a : C) (b : Bool) (hd : 0 < D (c,b)) :
    removeOne D (c,b) (a,false)+removeOne D (c,b) (a,true)=
      D (a,false)+D (a,true)-(if a=c then 1 else 0) := by
  by_cases ha : a=c
  · subst a
    cases b <;> simp only [removeOne,Prod.mk.injEq,Bool.false_eq_true,
      Bool.true_eq_false,↓reduceIte,and_false,Nat.sub_zero] at hd ⊢ <;> omega
  · simp only [removeOne,Prod.mk.injEq,ha,false_and,↓reduceIte,Nat.sub_zero]

variable {I J : Type u} [LinearOrder I] [LinearOrder J]

omit [LinearOrder I] [LinearOrder J] in
lemma balanced_of_pair_totals (small : I → J → Bool) (B : I → J → ℕ) (U : ℕ)
    (hB : ∀ i j, small i j=true → B i j=U) (z : SmallProfile small)
    (hpair : ∀ a : Cells small, z (a,false)+z (a,true)=U) : Balanced small B z := by
  intro i j
  cases hij : small i j
  · simp only [smallView,smallQ,hij,Bool.false_eq_true,↓reduceDIte]
  · have hh := hpair ⟨(i,j),hij⟩
    simp only [smallView,smallQ,hij,dite_eq_left,hB i j hij]
    omega

lemma pattern_after_one_removal (small : I → J → Bool) (B : I → J → ℕ) (U : ℕ)
    (hU : 1 ≤ U) (hB : ∀ i j, small i j=true → B i j=U)
    (s : I×J) (hs : small s.1 s.2=true) (D : SmallProfile small)
    (hpair : ∀ a : Cells small, D (a,false)+D (a,true)=if a=⟨s,hs⟩ then U+1 else U)
    (i : SmallView (fun a : I×J => small a.1 a.2)) (hi : 0 < D i)
    (hz : ∀ a, removeOne D i a ≤ U) : Pattern small B (removeOne D i) := by
  rcases i with ⟨c,b⟩
  by_cases hc : c=⟨s,hs⟩
  · subst c
    left
    apply balanced_of_pair_totals small B U hB
    intro a
    have hh := pair_total_removeOne D ⟨s,hs⟩ a b hi
    rw [hpair a] at hh
    by_cases ha : a=⟨s,hs⟩
    · rw [ite_eq_left ha,ite_eq_left ha] at hh
      omega
    · rw [ite_eq_right ha,ite_eq_right ha] at hh
      omega
  · right
    have hc' : c.val≠s := fun he => hc (Subtype.ext he)
    refine ⟨c.val,s,c.property,hs,?_⟩
    apply defect_of_pair_totals small B U hU hB c.val s c.property hs hc' _ hz
    intro a
    have hh := pair_total_removeOne D c a b hi
    rw [hpair a] at hh
    have hp : removeOne D (c,b) (a,false)+removeOne D (c,b) (a,true)=
        if a=c then U-1 else if a=⟨s,hs⟩ then U+1 else U := by
      by_cases hac : a=c
      · have has : a≠⟨s,hs⟩ := fun he => hc (hac.symm.trans he)
        rw [ite_eq_right has,ite_eq_left hac] at hh
        rw [ite_eq_left hac]
        exact hh
      · rw [ite_eq_right hac] at hh ⊢
        by_cases has : a=⟨s,hs⟩
        · rw [ite_eq_left has] at hh ⊢
          omega
        · rw [ite_eq_right has] at hh ⊢
          omega
    simpa only [Subtype.ext_iff] using hp

lemma assemble_bounded (small : I → J → Bool) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U : ℕ) (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U)
    {n : ℕ} (e : Fin n ≃ Later small s)
    (v : Coordinates Bool (widths (fun _ : Fin n => U)) → ℕ)
    (hv : InBox (bounds (fun _ : Bool => U) (widths (fun _ : Fin n => U))) v) :
    ∀ a, assemble small s hs σ U e v a ≤ U := by
  rw [bounds_constant] at hv
  intro a
  obtain ⟨w,rfl⟩ := (contextEquiv small s hs e U).surjective a
  rw [assemble_apply]
  cases w with
  | inl p =>
    rcases p with ⟨p,b⟩
    cases b
    · exact hσ p
    · exact Nat.sub_le _ _
  | inr w => exact hv w

lemma base_pair_total (small : I → J → Bool) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U l : ℕ) (hlU : l ≤ U)
    (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U) {n : ℕ} (e : Fin n ≃ Later small s)
    (q : Assignments (widths (fun _ : Fin n => U))) (a : Cells small) :
    assemble small s hs σ U e (embedding _ (rootDisplay U l) q) (a,false)+
      assemble small s hs σ U e (embedding _ (rootDisplay U l) q) (a,true)=
      if a=⟨s,hs⟩ then U+1 else U := by
  obtain ⟨v,rfl⟩ := (cellSplitEquiv small s hs).surjective a
  rcases v with p|(_|t)
  · have hps : p.val≠⟨s,hs⟩ := by
      intro he
      have h := p.property
      rw [he] at h
      exact h.ne rfl
    change assemble small s hs σ U e (embedding _ (rootDisplay U l) q) (p.val,false)+
      assemble small s hs σ U e (embedding _ (rootDisplay U l) q) (p.val,true)=
      if p.val=⟨s,hs⟩ then U+1 else U
    simp only [assemble_prefix,Bool.false_eq_true,↓reduceIte,hps]
    have hb := hσ p
    omega
  · change assemble small s hs σ U e (embedding _ (rootDisplay U l) q) (⟨s,hs⟩,false)+
      assemble small s hs σ U e (embedding _ (rootDisplay U l) q) (⟨s,hs⟩,true)=
      if (⟨s,hs⟩ : Cells small)=⟨s,hs⟩ then U+1 else U
    rw [ite_eq_left rfl]
    simp only [assemble_special,embedding_root,rootDisplay,Bool.false_eq_true,↓reduceIte]
    omega
  · have hts : t.val≠⟨s,hs⟩ := by
      intro he
      have h := t.property
      rw [he] at h
      exact h.ne rfl
    change assemble small s hs σ U e (embedding _ (rootDisplay U l) q) (t.val,false)+
      assemble small s hs σ U e (embedding _ (rootDisplay U l) q) (t.val,true)=
      if t.val=⟨s,hs⟩ then U+1 else U
    have hf := assemble_later small s hs σ U e (embedding _ (rootDisplay U l) q) (e.symm t) false
    have ht := assemble_later small s hs σ U e (embedding _ (rootDisplay U l) q) (e.symm t) true
    simp only [Equiv.apply_symm_apply] at hf ht
    rw [hf,ht,ite_eq_right hts]
    exact embedding_pair_total (fun _ : Fin n => U) (rootDisplay U l) q (e.symm t)

/-- Every box-valid transport leaf has exactly an allowed physical
small-graph pattern. No multi-defect vertex enters the local energy. -/
theorem leaf_pattern (small : I → J → Bool) (B : I → J → ℕ)
    (s : I×J) (hs : small s.1 s.2=true) (σ : I×J → ℕ) (U l : ℕ)
    (hU : 1 ≤ U) (hlU : l ≤ U) (hB : ∀ i j, small i j=true → B i j=U)
    (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U) {n : ℕ} (e : Fin n ≃ Later small s)
    (x : Coordinates Bool (widths (fun _ : Fin n => U)) → ℕ)
    (hx : x ∈ leafVertices _ (rootDisplay U l))
    (hbox : InBox (bounds (fun _ : Bool => U) (widths (fun _ : Fin n => U))) x) :
    Pattern small B (assemble small s hs σ U e x) := by
  obtain ⟨q,_,hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
  have hi' := (Finset.mem_filter.mp hi).2
  have hb := assemble_bounded small s hs σ U hσ e _ hbox
  rw [assemble_removeOne] at hb ⊢
  apply pattern_after_one_removal small B U hU hB s hs
    (assemble small s hs σ U e (embedding _ (rootDisplay U l) q))
    (base_pair_total small s hs σ U l hlU hσ e q)
    (contextEquiv small s hs e U (.inr i)) _ hb
  rw [assemble_apply]
  exact hi'

end ContingencyTables.SmallGraphProfiles

end OAI
