import OAI.Probability.ClassicalON.CoarseGeometry

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace ClassicalON

abbrev CoarseDirection := Fin 3 × Fin 3
abbrev CoarseCode (L : ℕ) := Fin L → CoarseDirection

def directionVector (d : CoarseDirection) : Site := ((d.1.val:ℤ)-1,(d.2.val:ℤ)-1)
def codePosition {L : ℕ} (z : Site) (c : CoarseCode L) (i : Fin (L+1)) : Site :=
  z+Fin.partialSum (directionVector ∘ c) i

@[simp] theorem codePosition_zero {L : ℕ} (z : Site) (c : CoarseCode L) : codePosition z c 0=z := by
  simp [codePosition]

theorem codePosition_succ {L : ℕ} (z : Site) (c : CoarseCode L) (i : Fin L) :
    codePosition z c i.succ=codePosition z c i.castSucc+directionVector (c i) := by
  simp only [codePosition,Fin.partialSum_succ,Function.comp_apply,add_assoc]

theorem directionVector_surj {z w : Site} (h : siteRadius z w≤1) :
    ∃ d,directionVector d=w-z := by
  have hh := (siteRadius_le_iff z w 1).mp h
  have h1 := abs_le.mp hh.1
  have h2 := abs_le.mp hh.2
  refine ⟨(⟨(w.1-z.1+1).toNat,by omega⟩,⟨(w.2-z.2+1).toNat,by omega⟩),?_⟩
  apply Prod.ext <;> dsimp [directionVector] <;> omega

theorem codePosition_exists {L : ℕ} (p : Fin (L+1) → Site)
    (h : ∀ i : Fin L,siteRadius (p i.castSucc) (p i.succ)≤1) :
    ∃ c : CoarseCode L,codePosition (p 0) c=p := by
  choose c hc using fun i => directionVector_surj (h i)
  refine ⟨c,funext fun i => ?_⟩
  induction i using Fin.induction with
  | zero => exact codePosition_zero _ _
  | succ i ih => rw [codePosition_succ,ih,hc]; abel

abbrev SimpleCoarseCode (z : Site) (L : ℕ) := {c : CoarseCode L // Function.Injective (codePosition z c)}

theorem card_simpleCoarseCode (z : Site) (L : ℕ) : Fintype.card (SimpleCoarseCode z L)≤9^L := by
  calc
    _≤Fintype.card (CoarseCode L) := Fintype.card_subtype_le _
    _=9^L := by simp [CoarseCode,CoarseDirection]

theorem codeColor_exists (t : ℕ) (z : Site) (c : CoarseCode (25*t)) :
    ∃ q : SiteColor,t≤Fintype.card {i : Fin (25*t+1) // siteColor (codePosition z c i)=q} := by
  obtain ⟨q,hq⟩ := Fintype.exists_le_card_fiber_of_mul_le_card
    (fun i => siteColor (codePosition z c i)) (n := t) (by simp [SiteColor])
  exact ⟨q,by simpa only [Fintype.card_subtype] using hq⟩

def codeColor (t : ℕ) (z : Site) (c : CoarseCode (25*t)) : SiteColor :=
  (codeColor_exists t z c).choose

theorem codeColor_card (t : ℕ) (z : Site) (c : CoarseCode (25*t)) :
    t≤Fintype.card {i : Fin (25*t+1) // siteColor (codePosition z c i)=codeColor t z c} :=
  (codeColor_exists t z c).choose_spec

end ClassicalON

end

end OAI
