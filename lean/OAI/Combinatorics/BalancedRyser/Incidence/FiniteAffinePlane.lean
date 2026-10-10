import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Prod

namespace OAI

namespace Balanced
namespace FiniteAffine

noncomputable section
attribute [local instance] Classical.propDecidable

structure Plane (q : ℕ) (P D L : Type*) [Fintype P] [Fintype D] [Fintype L] where
  direction : L → D
  incident : P → L → Prop
  card_points : Fintype.card P = q ^ 2
  card_directions : Fintype.card D = q + 1
  card_lines_direction : ∀ d,
    (Finset.univ.filter (fun ℓ : L => direction ℓ = d)).card = q
  card_points_line : ∀ ℓ,
    (Finset.univ.filter (fun p : P => incident p ℓ)).card = q
  unique_line_direction : ∀ p d, ∃! ℓ, direction ℓ = d ∧ incident p ℓ
  unique_join : ∀ p r, p ≠ r → ∃! ℓ, incident p ℓ ∧ incident r ℓ

variable {q : ℕ} {P D L : Type*} [Fintype P] [Fintype D] [Fintype L]

def Plane.linePoints (A : Plane q P D L) (ℓ : L) : Finset P :=
  Finset.univ.filter (fun p => A.incident p ℓ)

end
end FiniteAffine
end Balanced

end OAI
