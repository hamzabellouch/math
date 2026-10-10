import Mathlib

namespace OAI

namespace SharpRamseyFive.Windows
open scoped Classical BigOperators
noncomputable section

abbrev Slots (w r : ℕ) := (((Fin w×Bool)×Fin r)⊕(Fin w×Fin (2*r)))

def windowCoordinates {w r : ℕ} : Slots w r→Fin w×Fin (4*r)
  | Sum.inl ((v,false),a) => (v,⟨a.val,by omega⟩)
  | Sum.inl ((v,true),a) => (v,⟨3*r+a.val,by omega⟩)
  | Sum.inr (v,t) => (v,⟨r+t.val,by omega⟩)

lemma windowCoordinates_injective {w r : ℕ} : Function.Injective (@windowCoordinates w r) := by
  intro x y he
  have hw := congrArg (fun z=>z.1) he
  have hp := congrArg (fun z=>z.2.val) he
  rcases x with ⟨⟨v,b⟩,a⟩|⟨v,t⟩ <;> rcases y with ⟨⟨u,c⟩,d⟩|⟨u,s⟩
  · cases b <;> cases c
    all_goals simp only [windowCoordinates] at hw hp
    · subst u
      have : a=d := Fin.ext (by omega)
      subst d
      rfl
    · omega
    · omega
    · subst u
      have : a=d := Fin.ext (by omega)
      subst d
      rfl
  · cases b <;> simp only [windowCoordinates] at hw hp <;> omega
  · cases c <;> simp only [windowCoordinates] at hw hp <;> omega
  · simp only [windowCoordinates] at hw hp
    subst u
    have : t=s := Fin.ext (by omega)
    subst s
    rfl

def slotEmbedding {w r : ℕ} : Slots w r↪Fin (w*(4*r)) :=
  ⟨fun i=>finProdFinEquiv (windowCoordinates i),
    finProdFinEquiv.injective.comp windowCoordinates_injective⟩

lemma slotEmbedding_val {w r : ℕ} (i : Slots w r) :
    (slotEmbedding i).val=(windowCoordinates i).1.val*(4*r)+(windowCoordinates i).2.val := by
  change (windowCoordinates i).2.val+(4*r)*(windowCoordinates i).1.val=_
  ring

lemma representative_early {w r : ℕ} (v : Fin w) (a : Fin r) (t : Fin (2*r)) :
    slotEmbedding (Sum.inl ((v,false),a))<slotEmbedding (Sum.inr (v,t)) := by
  simp only [Fin.lt_def,slotEmbedding_val,windowCoordinates]
  omega

lemma representative_late {w r : ℕ} (v : Fin w) (a : Fin r) (t : Fin (2*r)) :
    slotEmbedding (Sum.inr (v,t))<slotEmbedding (Sum.inl ((v,true),a)) := by
  simp only [Fin.lt_def,slotEmbedding_val,windowCoordinates]
  omega

lemma ordered_windows {w r : ℕ} (i j : Slots w r)
    (h : (windowCoordinates i).1<(windowCoordinates j).1) :
    slotEmbedding i<slotEmbedding j := by
  simp only [Fin.lt_def,slotEmbedding_val] at h ⊢
  have hi := (windowCoordinates i).2.isLt
  have hj := (windowCoordinates j).2.isLt
  have hm : ((windowCoordinates i).1.val+1)*(4*r)≤(windowCoordinates j).1.val*(4*r) :=
    Nat.mul_le_mul_right _ h
  nlinarith

lemma middle_order {w r : ℕ} (v : Fin w) (s t : Fin (2*r)) (h : s<t) :
    slotEmbedding (Sum.inr (v,s))<slotEmbedding (Sum.inr (v,t)) := by
  simp only [Fin.lt_def,slotEmbedding_val,windowCoordinates] at h ⊢
  omega

lemma card_slots (w r : ℕ) : Fintype.card (Slots w r)=w*(4*r) := by
  simp only [Slots,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
  ring

lemma slotEmbedding_bijective (w r : ℕ) : Function.Bijective (@slotEmbedding w r) := by
  have hc : Fintype.card (Slots w r)=Fintype.card (Fin (w*(4*r))) := by
    rw [card_slots,Fintype.card_fin]
  exact (Fintype.bijective_iff_injective_and_card (@slotEmbedding w r)).mpr
    ⟨slotEmbedding.injective,hc⟩

end
end SharpRamseyFive.Windows

end OAI
