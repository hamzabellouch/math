import OAI.NumberTheory.Ostmann.Arithmetic.MovingRegularTransfer

namespace OAI

/-! # A shared dependent Fourier family for disjoint prime lists -/

namespace Ostmann

/-- The dependent disjoint union of two families, with its motive explicit. -/
def movingSumFactors {J I : Type*} (Q : J → ℕ) (L : I → ℕ)
    (gQ : ∀ j, ZMod (Q j) → ℂ) (gL : ∀ i, ZMod (L i) → ℂ) :
    ∀ i, ZMod (Sum.elim Q L i) → ℂ :=
  Sum.rec (motive := fun i => ZMod (Sum.elim Q L i) → ℂ) gQ gL

end Ostmann

end OAI
