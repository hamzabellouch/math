import Mathlib
import OAI.Analysis.LaughlinGap.RationalCreatedGram

namespace OAI

/-! Fast Four Keys. -/

noncomputable section


namespace LaughlinGap.RealOccupation

lemma fourKeys_of_index {D K : ℕ} (hD : D ≤ 23)
    (keys : Fin K → Finset (Fin 25)) (index : FourTerm D → Fin K)
    (rep : Fin K → FourTerm D)
    (cover : ∀ b, (fourTermLabels hD b).Nodup → (fourTermLabels hD b).toFinset=keys (index b))
    (hrep : ∀ a, (fourTermLabels hD (rep a)).Nodup ∧ (fourTermLabels hD (rep a)).toFinset=keys a) :
    fourKeys hD = Finset.univ.image keys := by
  ext A
  constructor
  · intro h
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_image.mpr ⟨index b,Finset.mem_univ _,(cover b (Finset.mem_filter.mp hb).2).symm⟩
  · intro h
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_image.mpr ⟨rep a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hrep a).1⟩,(hrep a).2⟩

end LaughlinGap.RealOccupation

namespace LaughlinGap.RealOccupation

def checkFourTerms (D : ℕ) (P : FourTerm D → Bool) : Bool :=
  (List.finRange (D+1)).all fun n =>
    (List.finRange ((n.val+1)/2)).all fun j =>
      (List.finRange ((D-n.val+2)/2)).all fun x => P ⟨n,j,x⟩

lemma checkFourTerms_sound {D : ℕ} (P : FourTerm D → Prop) [DecidablePred P]
    (h : checkFourTerms D (fun b => decide (P b)) = true) : ∀ b, P b := by
  rintro ⟨n,j,x⟩
  have hn := List.all_eq_true.mp h n (List.mem_finRange n)
  have hj := List.all_eq_true.mp hn j (List.mem_finRange j)
  exact of_decide_eq_true (List.all_eq_true.mp hj x (List.mem_finRange x))

end LaughlinGap.RealOccupation

namespace LaughlinGap.RealOccupation

def fourTermCode {D : ℕ} (b : FourTerm D) : ℕ × ℕ × ℕ :=
  (b.1.val,b.2.1.val,b.2.2.val)

lemma fourTermCode_injective (D : ℕ) : Function.Injective (@fourTermCode D) := by
  rintro ⟨⟨n,hn⟩,⟨j,hj⟩,⟨x,hx⟩⟩ ⟨⟨n',hn'⟩,⟨j',hj'⟩,⟨x',hx'⟩⟩ h
  simp only [fourTermCode, Prod.mk.injEq] at h
  obtain ⟨rfl,rfl,rfl⟩ := h
  rfl

lemma checkFourFiber_sound {D : ℕ} (hD : D ≤ 23) (A : Finset (Fin 25))
    (s : Finset (FourTerm D))
    (h : checkFourTerms D (fun b => decide
      ((fourTermLabels hD b).toFinset=A ↔ fourTermCode b ∈ s.image fourTermCode))=true) :
    ∀ b, (fourTermLabels hD b).toFinset=A ↔ b ∈ s := by
  intro b
  have hb := checkFourTerms_sound _ h b
  simpa only [Finset.mem_image, fourTermCode_injective D |>.eq_iff, exists_eq_right] using hb

end LaughlinGap.RealOccupation

namespace LaughlinGap.RealOccupation

lemma fourFibers_of_index {D K : ℕ} (hD : D ≤ 23)
    (keys : Fin K → Finset (Fin 25)) (index : FourTerm D → Fin K)
    (fibers : Fin K → Finset (FourTerm D))
    (hi : Function.Injective keys) (hcard : ∀ a, (keys a).card=4)
    (cover : ∀ b, (fourTermLabels hD b).Nodup → (fourTermLabels hD b).toFinset=keys (index b))
    (fiberCover : ∀ b, (fourTermLabels hD b).Nodup → b ∈ fibers (index b))
    (fiberSound : ∀ a, ∀ b ∈ fibers a, (fourTermLabels hD b).toFinset=keys a) :
    ∀ a b, (fourTermLabels hD b).toFinset=keys a ↔ b ∈ fibers a := by
  intro a b
  constructor
  · intro h
    have hn : (fourTermLabels hD b).Nodup := by
      apply (Multiset.toFinset_card_eq_card_iff_nodup (m := (↑(fourTermLabels hD b) : Multiset (Fin 25)))).mp
      change (fourTermLabels hD b).toFinset.card=(fourTermLabels hD b).length
      rw [h,hcard]
      rfl
    have hind : index b=a := hi ((cover b hn).symm.trans h)
    simpa only [hind] using fiberCover b hn
  · exact fiberSound a b

end LaughlinGap.RealOccupation

namespace LaughlinGap.RealOccupation

def checkFourFibersSound {D K : ℕ} (hD : D ≤ 23)
    (keys : Fin K → Finset (Fin 25)) (fibers : Fin K → Finset (FourTerm D)) : Bool :=
  (List.finRange K).all fun a => @decide (∀ b ∈ fibers a,
    (fourTermLabels hD b).toFinset=keys a) (Finset.decidableDforallFinset (s := fibers a))

lemma checkFourFibersSound_sound {D K : ℕ} (hD : D ≤ 23)
    (keys : Fin K → Finset (Fin 25)) (fibers : Fin K → Finset (FourTerm D))
    (h : checkFourFibersSound hD keys fibers=true) :
    ∀ a b, b ∈ fibers a → (fourTermLabels hD b).toFinset=keys a := by
  intro a b hb
  have ha := List.all_eq_true.mp h a (List.mem_finRange a)
  exact @of_decide_eq_true _ (Finset.decidableDforallFinset (s := fibers a)) ha b hb

end LaughlinGap.RealOccupation

end

end OAI
