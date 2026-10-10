import Mathlib

namespace OAI

namespace SnakyConditional
variable {α : Type*} [DecidableEq α]
inductive WinsIn (win : Finset α → Prop) : ℕ → Finset α → Finset α → Prop
  | done {n M B} : win M → WinsIn win n M B
  | move {n M B} (x : α) (hxM : x ∉ M) (hxB : x ∉ B)
      (next : ∀ b, b ∉ insert x M → b ∉ B →
        WinsIn win n (insert x M) (insert b B)) :
      WinsIn win (n + 1) M B
def Template (win : Finset α → Prop) (n : ℕ) (A H : Finset α) : Prop :=
  ∀ M B, Disjoint M B → A ⊆ M → Disjoint B H → WinsIn win n M B
abbrev Cell := ℤ × ℤ
def snaky : Finset Cell := {(0, 0), (1, 0), (2, 0), (3, 0), (3, 1), (4, 1)}
def orient (r : Fin 8) (p : Cell) : Cell :=
  match r.val with
  | 0 => (p.1, p.2)
  | 1 => (p.2, p.1)
  | 2 => (p.1, -p.2)
  | 3 => (-p.2, p.1)
  | 4 => (-p.1, p.2)
  | 5 => (p.2, -p.1)
  | 6 => (-p.1, -p.2)
  | _ => (-p.2, -p.1)
def placement (r : Fin 8) (t p : Cell) : Cell := orient r p + t
def HasSnaky (M : Finset Cell) : Prop :=
  ∃ (r : Fin 8) (t : Cell), snaky.image (placement r t) ⊆ M
end SnakyConditional

end OAI
