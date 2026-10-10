import OAI.Combinatorics.ContingencyTables.Transport.ExcessContextProfiles
import OAI.Combinatorics.ContingencyTables.Transport.IntegerSliceReindex

namespace OAI

/-! # The physical small graph and contextual unit exchanges -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open PhysicalCompletionFibres LargePairEnumeration BalancedFamily BalancedBox
open IntegerWeightedTransport FirstPaperProfiles ExcessContextProfiles FactorialSignatures

universe u

variable {I J : Type u} [LinearOrder I] [LinearOrder J]

def Balanced (small : I → J → Bool) (B : I → J → ℕ) (z : SmallProfile small) : Prop :=
  ∀ i j, smallView small z false i j=smallQ small B z i j

def SingleDefect (small : I → J → Bool) (B : I → J → ℕ) (z : SmallProfile small) : Prop :=
  ∃ s t : I×J, small s.1 s.2=true ∧ small t.1 t.2=true ∧
    IsDefect (smallView small z false) (smallQ small B z) s t

def Pattern (small : I → J → Bool) (B : I → J → ℕ) (z : SmallProfile small) : Prop :=
  Balanced small B z ∨ SingleDefect small B z

abbrev Profiles (small : I → J → Bool) (B : I → J → ℕ) :=
  {z : BoundedProfile small B // Pattern small B (naturalProfile z)}

lemma balanced_not_defect (small : I → J → Bool) (B : I → J → ℕ) (z : SmallProfile small)
    (hb : Balanced small B z) : ¬SingleDefect small B z := by
  rintro ⟨s,t,_,_,hd⟩
  have h := hd.negative_entry
  rw [hb s.1 s.2] at h
  omega

lemma assemble_injective (small : I → J → Bool) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U : ℕ) {n : ℕ} (e : Fin n ≃ Later small s) :
    Function.Injective (assemble small s hs σ U e) := by
  intro v w he
  funext a
  have hh := congrFun he (contextEquiv small s hs e U (.inr a))
  simpa only [assemble,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inr] using hh

/-- Fixing a prefix and reindexing preserves every actual unit removal. -/
lemma assemble_removeOne (small : I → J → Bool) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U : ℕ) {n : ℕ} (e : Fin n ≃ Later small s)
    (v : Coordinates Bool (widths (fun _ : Fin n => U)) → ℕ)
    (i : Coordinates Bool (widths (fun _ : Fin n => U))) :
    assemble small s hs σ U e (removeOne v i)=
      removeOne (assemble small s hs σ U e v) (contextEquiv small s hs e U (.inr i)) := by
  have he : Sum.elim (prefixRaw small s σ U) (removeOne v i)=
      removeOne (Sum.elim (prefixRaw small s σ U) v) (.inr i) := by
    funext a
    cases a with
    | inl a => simp only [removeOne,Sum.elim_inl,Sum.inl_ne_inr,↓reduceIte,Nat.sub_zero]
    | inr a => simp only [removeOne,Sum.elim_inr,Sum.inr.injEq]
  unfold assemble
  rw [he]
  exact removeOne_reindex (contextEquiv small s hs e U) _ (.inr i)

/-- Every contextual transport edge is an actual doubled-small-coordinate
unit exchange, with no move involving the retained prefix. -/
theorem assemble_exchange_adjacent (small : I → J → Bool) (s : I×J)
    (hs : small s.1 s.2=true) (σ : I×J → ℕ) (U : ℕ) {n : ℕ}
    (e : Fin n ≃ Later small s)
    (X Y : Coordinates Bool (widths (fun _ : Fin n => U)) → ℕ)
    (hxy : IntegerExchangeAdjacent X Y) :
    IntegerExchangeAdjacent (assemble small s hs σ U e X) (assemble small s hs σ U e Y) := by
  obtain ⟨D,i,j,hij,hi,hj,rfl,rfl⟩ := hxy
  refine ⟨assemble small s hs σ U e D,contextEquiv small s hs e U (.inr i),
    contextEquiv small s hs e U (.inr j),?_,?_,?_,?_,?_⟩
  · intro he
    exact hij (Sum.inr.inj ((contextEquiv small s hs e U).injective he))
  · rw [assemble_apply]
    exact hi
  · rw [assemble_apply]
    exact hj
  · exact assemble_removeOne small s hs σ U e D i
  · exact assemble_removeOne small s hs σ U e D j

end ContingencyTables.SmallGraphProfiles

end OAI
