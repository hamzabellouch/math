import Mathlib

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset
open scoped Classical BigOperators
noncomputable section

abbrev Slot (w n : ℕ) := Fin w × Fin (4*n)
abbrev Block (w : ℕ) := Fin w × Bool

def quarter (n : ℕ) (b : Bool) (x : Fin n) : Fin (4*n) :=
  if b then ⟨3*n+x.val,by omega⟩ else ⟨x.val,by omega⟩

lemma quarter_injective (n : ℕ) : Function.Injective (fun bx : Bool×Fin n=>quarter n bx.1 bx.2) := by
  rintro ⟨b,x⟩ ⟨c,y⟩ h
  have hv : (quarter n b x).val = (quarter n c y).val := congrArg Fin.val h
  cases b <;> cases c <;> simp only [quarter,Bool.false_eq_true,↓reduceIte] at hv
  · have hh : x = y := Fin.ext hv
    cases hh
    rfl
  · omega
  · omega
  · have hh : x = y := Fin.ext (by omega)
    cases hh
    rfl

def embedding (w n : ℕ) : Block w × Fin n ↪ Slot w n where
  toFun bx := (bx.1.1,quarter n bx.1.2 bx.2)
  inj' := by
    rintro ⟨⟨i,b⟩,x⟩ ⟨⟨j,c⟩,y⟩ h
    have hi : i = j := congrArg Prod.fst h
    have hb : (b,x) = (c,y) := quarter_injective n (congrArg Prod.snd h)
    cases hi
    cases hb
    rfl

def owner (w n : ℕ) (i : Slot w n) : Option (Block w) :=
  if i.2.val < n then some (i.1,false) else
    if 3*n ≤ i.2.val then some (i.1,true) else none

lemma embedding_owner (w n : ℕ) (b : Block w) (x : Fin n) :
    owner w n (embedding w n (b,x))=some b := by
  rcases b with ⟨i,b⟩
  cases b
  · change (if x.val < n then some (i,false) else
      if 3*n ≤ x.val then some (i,true) else none) = some (i,false)
    rw [ite_eq_left x.isLt]
  · change (if 3*n+x.val < n then some (i,false) else
      if 3*n ≤ 3*n+x.val then some (i,true) else none) = some (i,true)
    rw [ite_eq_right (by omega),ite_eq_left (by omega)]

def middle (w n : ℕ) : Fin w × Fin (2*n) ↪ Slot w n where
  toFun ix := (ix.1,⟨n+ix.2.val,by omega⟩)
  inj' := by
    rintro ⟨i,x⟩ ⟨j,y⟩ h
    have hi : i = j := congrArg Prod.fst h
    have hx : n+x.val = n+y.val := congrArg (fun z:Slot w n=>z.2.val) h
    have hxy : x = y := Fin.ext (by omega)
    exact Prod.ext hi hxy

lemma middle_unowned (w n : ℕ) (i : Fin w) (x : Fin (2*n)) :
    owner w n (middle w n (i,x))=none := by
  change (if n+x.val < n then some (i,false) else
    if 3*n ≤ n+x.val then some (i,true) else none) = none
  rw [ite_eq_right (by omega),ite_eq_right (by omega)]

def position {w n : ℕ} (x : Slot w n) : ℕ := x.1.val*(4*n)+x.2.val

lemma position_injective (w n : ℕ) : Function.Injective (@position w n) := by
  rintro ⟨i,x⟩ ⟨j,y⟩ h
  have hi : i.val=j.val := by
    dsimp [position] at h
    have hx:=x.isLt
    have hy:=y.isLt
    rcases lt_trichotomy i.val j.val with hh|hh|hh
    · have : i.val+1 ≤ j.val := by omega
      nlinarith
    · exact hh
    · have : j.val+1 ≤ i.val := by omega
      nlinarith
  have hxy : x = y := Fin.ext (by dsimp [position] at h; rw [hi] at h; omega)
  exact Prod.ext (Fin.ext hi) hxy

lemma between (w n : ℕ) (i : Fin w) (x y : Fin n) (t : Fin (2*n)) :
    position (embedding w n ((i,false),x)) < position (middle w n (i,t)) ∧
    position (middle w n (i,t)) < position (embedding w n ((i,true),y)) := by
  change i.val*(4*n)+x.val < i.val*(4*n)+(n+t.val) ∧
    i.val*(4*n)+(n+t.val) < i.val*(4*n)+(3*n+y.val)
  constructor <;> omega

lemma before_next (w n : ℕ) (i j : Fin w) (hij : i < j) (b c : Bool) (x y : Fin n) :
    position (embedding w n ((i,b),x)) < position (embedding w n ((j,c),y)) := by
  have hix : (quarter n b x).val < 4*n := (quarter n b x).isLt
  have hiy : 0 ≤ (quarter n c y).val := Nat.zero_le _
  change i.val*(4*n)+(quarter n b x).val < j.val*(4*n)+(quarter n c y).val
  have hi : i.val+1 ≤ j.val := hij
  nlinarith

lemma middle_card (w n : ℕ) : (univ.map (middle w n)).card=w*(2*n) := by simp

end
end SharpLogRamsey.Selection.Windows

end

end OAI
