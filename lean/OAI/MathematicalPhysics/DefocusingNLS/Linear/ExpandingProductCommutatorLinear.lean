import OAI.MathematicalPhysics.DefocusingNLS.Linear.TorusProductCommutator

namespace OAI

/-! # Linearity of the physical product commutator in the field -/

namespace DefocusingNLS

theorem expandingProductCommutator_add (a L : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hN : 8 < (N : ℝ)) (hL : 1 ≤ L)
    (j : Fin N → Fin 12) (q f g : FourierL2) :
    expandingProductCommutator a L N ha ha1 hN hL j q (f + g) =
      expandingProductCommutator a L N ha ha1 hN hL j q f +
        expandingProductCommutator a L N ha ha1 hN hL j q g := by
  apply torusFourierIsometry.injective
  rw [map_add]
  simp only [torusProductCommutator_physical, expandingProduct_add_right, map_add]
  abel

end DefocusingNLS

end OAI
