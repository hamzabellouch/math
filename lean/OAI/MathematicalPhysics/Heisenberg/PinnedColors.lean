import OAI.MathematicalPhysics.Heisenberg.SlotColorTrace

namespace OAI

section

noncomputable section
open scoped Classical BigOperators
namespace Heisenberg.Surface
open Heisenberg.Cycle Heisenberg.Pin Heisenberg.Return
variable {V : Type*} [Fintype V]

abbrev PinnedColor (π : Equiv.Perm V) (P : Set V) :=
  {c : V → Bool // (∀ i,c (π i)=c i) ∧ ∀ i∈P,c i=true}
instance (π : Equiv.Perm V) (P : Set V) : Fintype (PinnedColor π P) := Fintype.ofFinite _
local instance (π : Equiv.Perm V) (P : Set V) : Fintype (MissingClasses π P) := Fintype.ofFinite _

lemma pinnedColor_sameCycle (π : Equiv.Perm V) (P : Set V) (c : PinnedColor π P)
    {i j : V} (h : π.SameCycle i j) : c.val i=c.val j :=
  SlotColor.const_cycle π ⟨c.val,c.property.1⟩ h

def pinnedColorEquiv (π : Equiv.Perm V) (P : Set V) :
    PinnedColor π P ≃ (MissingClasses π P → Bool) where
  toFun c q := Quotient.lift c.val (fun _ _ h=>pinnedColor_sameCycle π P c h) q.val
  invFun ε := ⟨fun i=>if h : ∀ j∈P,classOf π i≠classOf π j then ε ⟨classOf π i,h⟩ else true,by
    constructor
    · intro i; simp only [classOf_apply]
    · intro i hi; exact dite_eq_right (by intro h; exact h i hi rfl)⟩
  left_inv c := by
    apply Subtype.ext
    funext i
    dsimp
    split_ifs with h
    · rfl
    · obtain ⟨j,hj,hij⟩:=by simpa only [not_forall,not_not] using h
      exact ((pinnedColor_sameCycle π P c ((classOf_eq_iff π i j).mp hij)).trans (c.property.2 j hj)).symm
  right_inv ε := by
    funext q
    rcases q with ⟨q,hq⟩
    induction q using Quotient.inductionOn with | _ i =>
      dsimp
      split_ifs with h
      · rfl
      · exact (h hq).elim

lemma card_pinnedColor (π : Equiv.Perm V) (P : Set V) :
    Fintype.card (PinnedColor π P)=2^missingCount π P := by
  rw [Fintype.card_congr (pinnedColorEquiv π P),Fintype.card_fun,Fintype.card_bool]
  rw [missingCount,Nat.card_eq_fintype_card]

def halfSpin (b : Bool) : ℝ := if b then 1/2 else -1/2

lemma sum_halfSpin_bit {X : Type*} [Fintype X] (x : X) :
    (∑ ε : X → Bool,halfSpin (ε x))=0 := by
  let e : Equiv.Perm (X → Bool):=Equiv.piCongrRight (fun i=>if i=x then Equiv.boolNot else Equiv.refl Bool)
  have hn (ε : X → Bool) : halfSpin (e ε x)= -halfSpin (ε x) := by
    have he : e ε x= !(ε x) := by simp [e]
    rw [he]
    cases ε x <;> norm_num [halfSpin]
  have hh:=Equiv.sum_comp e (fun ε : X → Bool=>halfSpin (ε x))
  simp_rw [hn,Finset.sum_neg_distrib] at hh
  linarith

lemma missing_iff_nohit (π : Equiv.Perm V) (P : Set V) (i : V) :
    (∀ j∈P,classOf π i≠classOf π j) ↔ ¬HasHit π P i := by
  rw [hasHit_iff_cycle]
  simp only [not_exists,not_and]
  constructor
  · intro h j hj hs; exact h j hj ((classOf_eq_iff π i j).mpr hs)
  · intro h j hj he; exact h j hj ((classOf_eq_iff π i j).mp he)

theorem sum_pinned_spin (π : Equiv.Perm V) (P : Set V) (i : V) :
    (∑ c : PinnedColor π P,halfSpin (c.val i))=
      if HasHit π P i then (2:ℝ)^missingCount π P/2 else 0 := by
  rw [←(pinnedColorEquiv π P).symm.sum_comp (fun c=>halfSpin (c.val i))]
  by_cases hh : HasHit π P i
  · have hm : ¬∀ j∈P,classOf π i≠classOf π j := fun h=>(missing_iff_nohit π P i).mp h hh
    simp [hh,pinnedColorEquiv,hm,halfSpin,Fintype.card_bool,missingCount,
      Nat.card_eq_fintype_card,div_eq_mul_inv]
  · have hm:=(missing_iff_nohit π P i).mpr hh
    rw [ite_eq_right hh]
    change (∑ ε : MissingClasses π P → Bool, halfSpin (if h : ∀ j∈P,classOf π i≠classOf π j then ε ⟨classOf π i,h⟩ else true))=0
    simp only [dite_eq_left hm]
    with_reducible convert sum_halfSpin_bit (X:=MissingClasses π P) ⟨classOf π i,hm⟩ using 1
    congr! 20

theorem pinned_trace (π : Equiv.Perm V) (P : Set V) (f : (V → Bool) → ℝ) :
    Matrix.trace (SlotColor.matrix π * Matrix.diagonal (fun c=>if ∀ i∈P,c i=true then f c else 0))=
      ∑ c : PinnedColor π P,f c.val := by
  rw [SlotColor.trace_diagonal]
  have he : (∑ c : V → Bool,if ∀ i,c (π i)=c i then (if ∀ i∈P,c i=true then f c else 0) else 0)=
      ∑ c : V → Bool,if (∀ i,c (π i)=c i) ∧ (∀ i∈P,c i=true) then f c else 0 := by
    apply Finset.sum_congr rfl
    intro c _
    split_ifs <;> simp_all
  rw [he,←Finset.sum_filter]
  exact Finset.sum_subtype _ (fun c=>by simp) f

end Heisenberg.Surface
end
end

end OAI
