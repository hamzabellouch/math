import Mathlib

namespace OAI

namespace Ostmann.Characters
section Field
variable {F : Type*} [Field F]

theorem transfer_left_phase {P s v w HL HR : F}
    (h : s*P = v*HR-w*HL) (hleft : HL=0) (hP : P≠0) (hHR : HR≠0) :
    v/P = s/HR := by
  subst HL
  field_simp
  linear_combination -h

theorem transfer_right_phase {P s v w HL HR : F}
    (h : s*P = v*HR-w*HL) (hright : HR=0) (hP : P≠0) (hHL : HL≠0) :
    -w/P = s/HL := by
  subst HR
  field_simp
  linear_combination -h

theorem transfer_shared_phase {P s v w HL HR : F}
    (h : s*P = v*HR-w*HL) (hP : P≠0) (hHL : HL≠0) (hHR : HR≠0) :
    v/(P*HL)-w/(P*HR) = s/(HL*HR) := by
  field_simp
  linear_combination -h
end Field

def copySign (b : Bool) : ℤ := if b then 1 else -1

def transferGraph {H Y : Type*} [DecidableEq H]
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ) :
    ((H × Bool) ⊕ Y) → ((H × Bool) ⊕ Y) → ℤ
  | .inl (i,t), .inl (h,u) =>
      if t=u then if i=h then 0 else copySign t*b (some (.inl i)) (some (.inl h))
      else copySign t*b (some (.inl i)) none
  | .inl (i,t), .inr y => copySign t*b (some (.inl i)) (some (.inr y))
  | .inr y, .inl (i,t) => copySign t*b (some (.inr y)) (some (.inl i))
  | .inr _, .inr _ => 0

theorem transferGraph_regular {H Y : Type*} [DecidableEq H]
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ)
    (i : H) (ε : ℤ)
    (hrow : ∀ z, z ≠ some (.inl i) → b (some (.inl i)) z = ε)
    (t : Bool) (z : (H × Bool) ⊕ Y) (hz : z ≠ .inl (i,t)) :
    transferGraph b (.inl (i,t)) z = copySign t*ε := by
  cases z with
  | inr y => simp [transferGraph, hrow]
  | inl z =>
    rcases z with ⟨h,u⟩
    by_cases htu : t=u
    · subst u
      have hhi : h≠i := by intro e; subst h; exact hz rfl
      simp [transferGraph, hhi, Ne.symm hhi, hrow]
    · simp [transferGraph, htu, hrow]

theorem transferGraph_shared {H Y : Type*} [DecidableEq H]
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ) (y y' : Y) :
    transferGraph b (.inr y) (.inr y') = 0 := rfl
end Ostmann.Characters

end OAI
