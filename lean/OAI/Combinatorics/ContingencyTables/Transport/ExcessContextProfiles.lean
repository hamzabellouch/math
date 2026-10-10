import OAI.Combinatorics.ContingencyTables.Sampling.SmallContextEnumeration
import OAI.Combinatorics.ContingencyTables.Transport.ExcessPairCoordinates

namespace OAI

/-! # Physical defect profiles in the auxiliary context kernel -/

namespace ContingencyTables.ExcessContextProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open PhysicalCompletionFibres LargePairEnumeration BalancedFamily BalancedBox
open BalancedEnumeration IntegerWeightedTransport FirstPaperProfiles

universe u

variable {I J : Type u} [LinearOrder I] [LinearOrder J]

noncomputable def assemble (small : I → J → Bool) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U : ℕ) {n : ℕ} (e : Fin n ≃ Later small s)
    (v : Coordinates Bool (widths (fun _ : Fin n => U)) → ℕ) : SmallProfile small :=
  (Sum.elim (prefixRaw small s σ U) v) ∘ (contextEquiv small s hs e U).symm

lemma assemble_apply (small : I → J → Bool) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U : ℕ) {n : ℕ} (e : Fin n ≃ Later small s)
    (v : Coordinates Bool (widths (fun _ : Fin n => U)) → ℕ)
    (a : (Earlier small s×Bool) ⊕ Coordinates Bool (widths (fun _ : Fin n => U))) :
    assemble small s hs σ U e v (contextEquiv small s hs e U a)=
      Sum.elim (prefixRaw small s σ U) v a := by
  simp only [assemble,Function.comp_apply,Equiv.symm_apply_apply]

lemma assemble_prefix (small : I → J → Bool) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U : ℕ) {n : ℕ} (e : Fin n ≃ Later small s)
    (v : Coordinates Bool (widths (fun _ : Fin n => U)) → ℕ)
    (a : Earlier small s) (b : Bool) :
    assemble small s hs σ U e v (a.val,b)=if b then U-σ a.val.val else σ a.val.val := by
  have h := assemble_apply small s hs σ U e v (.inl (a,b))
  simpa only [contextEquiv_prefix,Sum.elim_inl,prefixRaw] using h

lemma assemble_special (small : I → J → Bool) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U : ℕ) {n : ℕ} (e : Fin n ≃ Later small s)
    (v : Coordinates Bool (widths (fun _ : Fin n => U)) → ℕ) (b : Bool) :
    assemble small s hs σ U e v (⟨s,hs⟩,b)=
      v ((coordinateEquiv Bool (fun _ : Fin n => U)).symm (.inl b)) := by
  have h := assemble_apply small s hs σ U e v
    (.inr ((coordinateEquiv Bool (fun _ : Fin n => U)).symm (.inl b)))
  simpa only [contextEquiv_special,Sum.elim_inr] using h

lemma assemble_later (small : I → J → Bool) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U : ℕ) {n : ℕ} (e : Fin n ≃ Later small s)
    (v : Coordinates Bool (widths (fun _ : Fin n => U)) → ℕ) (i : Fin n) (b : Bool) :
    assemble small s hs σ U e v ((e i).val,b)=
      v ((coordinateEquiv Bool (fun _ : Fin n => U)).symm (.inr (i,b))) := by
  have h := assemble_apply small s hs σ U e v
    (.inr ((coordinateEquiv Bool (fun _ : Fin n => U)).symm (.inr (i,b))))
  simpa only [contextEquiv_later,Sum.elim_inr] using h

def auxRoot (U l : ℕ) : Bool → ℕ := fun b => if b then U-l else l-1

lemma auxRoot_inBox (U l : ℕ) (hl : l ≤ U) : InBox (fun _ => U) (auxRoot U l) := by
  intro b
  cases b
  · exact (Nat.sub_le _ _).trans hl
  · exact Nat.sub_le _ _

noncomputable def rawExcess (small : I → J → Bool) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U l : ℕ) {n : ℕ} (e : Fin n ≃ Later small s)
    (q : ExcessAssignments (widths (fun _ : Fin n => U))) : SmallProfile small :=
  assemble small s hs σ U e (excessEmbedding _ (auxRoot U l) q)

lemma bounds_constant (U : ℕ) {n : ℕ} :
    bounds (fun _ : Bool => U) (widths (fun _ : Fin n => U))=(fun _ => U) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext a
    cases a with
    | inl a => exact congrFun ih a
    | inr b => cases b <;> rfl

lemma rawExcess_bounded (small : I → J → Bool) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U l : ℕ) (hl : l ≤ U)
    (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U) {n : ℕ} (e : Fin n ≃ Later small s)
    (q : ExcessAssignments (widths (fun _ : Fin n => U)))
    (hq : ValidExcess _ q) (a : SmallView (fun a : I×J => small a.1 a.2)) :
    rawExcess small s hs σ U l e q a ≤ U := by
  have hv := (excessEmbedding_inBox_iff _ _ _ (auxRoot_inBox U l hl) q).mpr hq
  obtain ⟨v,rfl⟩ := (contextEquiv small s hs e U).surjective a
  unfold rawExcess
  rw [assemble_apply]
  cases v with
  | inl p =>
    rcases p with ⟨p,b⟩
    cases b
    · exact hσ p
    · exact Nat.sub_le _ _
  | inr v =>
    rw [bounds_constant] at hv
    exact hv v

/-- The auxiliary profile has exactly the negative current pair and
one positive later pair required by the manuscript's conditional repair. -/
lemma rawExcess_pair_total (small : I → J → Bool) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U l : ℕ) (hl0 : 1 ≤ l) (hlU : l ≤ U)
    (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U) {n : ℕ} (e : Fin n ≃ Later small s)
    (q : ExcessAssignments (widths (fun _ : Fin n => U))) (a : Cells small) :
    rawExcess small s hs σ U l e q (a,false)+rawExcess small s hs σ U l e q (a,true)=
      if a=⟨s,hs⟩ then U-1 else
      if a=(e (excessIndex (fun _ : Fin n => U) q)).val then U+1 else U := by
  obtain ⟨v,rfl⟩ := (cellSplitEquiv small s hs).surjective a
  rcases v with p|(_|t)
  · have hps : p.val≠⟨s,hs⟩ := by
      intro he
      have h := p.property
      rw [he] at h
      exact h.ne rfl
    have hpt : p.val≠(e (excessIndex (fun _ : Fin n => U) q)).val := by
      intro he
      have h := p.property
      rw [he] at h
      exact (h.trans (e (excessIndex (fun _ : Fin n => U) q)).property).ne rfl
    change rawExcess small s hs σ U l e q (p.val,false)+rawExcess small s hs σ U l e q (p.val,true)=
      if p.val=⟨s,hs⟩ then U-1 else
      if p.val=(e (excessIndex (fun _ : Fin n => U) q)).val then U+1 else U
    simp only [rawExcess,assemble_prefix,Bool.false_eq_true,↓reduceIte,hps,hpt]
    have hb := hσ p
    omega
  · change rawExcess small s hs σ U l e q (⟨s,hs⟩,false)+rawExcess small s hs σ U l e q (⟨s,hs⟩,true)=
      if (⟨s,hs⟩ : Cells small)=⟨s,hs⟩ then U-1 else
      if (⟨s,hs⟩ : Cells small)=(e (excessIndex (fun _ : Fin n => U) q)).val then U+1 else U
    rw [ite_eq_left rfl]
    simp only [rawExcess,assemble_special,excessEmbedding_root,auxRoot,Bool.false_eq_true,↓reduceIte]
    omega
  · have hts : t.val≠⟨s,hs⟩ := by
      intro he
      have h := t.property
      rw [he] at h
      exact h.ne rfl
    have hte : t.val=(e (excessIndex (fun _ : Fin n => U) q)).val ↔
        e.symm t=excessIndex (fun _ : Fin n => U) q := by
      constructor
      · intro he
        have he' : t=e (excessIndex (fun _ : Fin n => U) q) := Subtype.ext he
        rw [he',Equiv.symm_apply_apply]
      · intro he
        have hh := congrArg e he
        simpa only [Equiv.apply_symm_apply] using congrArg Subtype.val hh
    have hh := excessEmbedding_pair_total (fun _ : Fin n => U) (auxRoot U l) q (e.symm t)
    change assemble small s hs σ U e (excessEmbedding _ (auxRoot U l) q) (t.val,false)+
      assemble small s hs σ U e (excessEmbedding _ (auxRoot U l) q) (t.val,true)=
      if t.val=⟨s,hs⟩ then U-1 else
      if t.val=(e (excessIndex (fun _ : Fin n => U) q)).val then U+1 else U
    have hf := assemble_later small s hs σ U e (excessEmbedding _ (auxRoot U l) q) (e.symm t) false
    have ht := assemble_later small s hs σ U e (excessEmbedding _ (auxRoot U l) q) (e.symm t) true
    simp only [Equiv.apply_symm_apply] at hf ht
    rw [hf,ht,ite_eq_right hts]
    by_cases h : e.symm t=excessIndex (fun _ : Fin n => U) q
    · rw [ite_eq_left (hte.mpr h)]
      simpa only [h,↓reduceIte] using hh
    · rw [ite_eq_right (fun he => h (hte.mp he))]
      simpa only [h,↓reduceIte,add_zero] using hh

end ContingencyTables.ExcessContextProfiles

end OAI
